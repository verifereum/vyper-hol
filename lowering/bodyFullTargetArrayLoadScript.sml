(* Optional array-length code, checked at the post-index runtime state. *)
Theory bodyFullTargetArrayLoad
Ancestors
  exprSimArrayIndex bodyFullUnwrapRun fragGasSeqPtr fragGasOriginPtr
  fragExecMem fragExec exprLoweringProps emitHelperProps emitHelper compileEnv
  venomState venomInst venomExecSemantics fragGasPathPtr ptrSafeRun
  finite_map list rich_list words arithmetic typedCopyOriginPtrBase typedMemoryCopy
  ptrDiscipline codegenRel pred_set

Theorem array_length_static_joint:
  comp_return (Lit (n2w cnt)) sa = (p,sb) /\
  ~s.vs_halted ==>
  sb = sa /\ eval_operand p s = SOME (n2w cnt) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s,G,tn)
Proof
  simp[comp_return_def] >> strip_tac >> gvs[eval_operand_def] >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

(* The caller instantiates opc with the actual location's loader opcode,
   and w with the read of the current (not pre-index) state. *)
Theorem array_length_emit_joint:
  emit_op opc [bop] sa = (p,sb) /\
  fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc [bop] [out]) s =
         OK (update_var out w s)) /\
  (!out. ptr_inst_ok D lo 0 ctx func G tn
         (mk_inst sa.cs_next_id opc [bop] [out]) s) /\
  (!out. inst_mem_below_frontier (mk_inst sa.cs_next_id opc [bop] [out]) s /\
         inst_dload_in_section (mk_inst sa.cs_next_id opc [bop] [out]) s) ==>
  ?out t G' tn'.
    p = Var out /\
    t = (update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id opc [bop] [out])
           (update_var out w s) /\
    tn' = step_taint (mk_inst sa.cs_next_id opc [bop] [out]) s
            (update_var out w s) tn /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
    eval_operand p t = SOME w /\
    ((t with vs_inst_idx := s.vs_inst_idx) with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all typed_copy_origin_ptr_emit_op_path >>
  disch_then (qspecl_then [`0`, `0`, `explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`out`, `t`, `G'`, `tn'`] >>
  gvs[typed_copy_state_frame_def, update_var_def,
      venom_state_component_equality]
QED

Theorem array_length_read_ghost_frame[local]:
  MEM opc [ADD; MLOAD; SLOAD; TLOAD; CALLDATALOAD; ILOAD; DLOAD] ==>
  (step_taint (mk_inst id opc args [out]) s
    (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc args [out]) s
    (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc args [out]) s
    (update_var out w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc args [out]) s
    (update_var out w s) tn).t_imm = tn.t_imm /\
  (!x. x <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id opc args [out])
      (update_var out w s)) x = FLOOKUP G x /\
    FLOOKUP (step_taint (mk_inst id opc args [out]) s
      (update_var out w s) tn).t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, step_taint_def, mk_inst_def,
       set_var_taint_def, store_taint_def, adopt_reset_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, imm_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rpt CASE_TAC >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED


(* Concrete generated-output boundary: safety is checked only for the
   instruction which the compiler actually emitted. *)
Theorem array_length_emit_concrete[local]:
  emit_op opc args sa = (Var out,sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
    OK (update_var out w s) /\
  access_ok lo G func (mk_inst sa.cs_next_id opc args [out]) s /\
  taint_ok func tn (mk_inst sa.cs_next_id opc args [out]) s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  inst_mem_below_frontier (mk_inst sa.cs_next_id opc args [out]) s /\
  inst_dload_in_section (mk_inst sa.cs_next_id opc args [out]) s ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := LENGTH sb.cs_current_insts),
     step_prov PG G (mk_inst sa.cs_next_id opc args [out]) (update_var out w s),
     step_taint (mk_inst sa.cs_next_id opc args [out]) s (update_var out w s) tn)
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id opc args [out]) s` by
    (simp[ptr_inst_ok_def, mk_inst_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id opc args [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> gvs[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc args [out]) (update_var out w s),
     step_taint (mk_inst sa.cs_next_id opc args [out]) s (update_var out w s) tn)` by
    (mp_tac (straight_line_origin_ptr_edge |> Q.INST
       [`i` |-> `mk_inst sa.cs_next_id opc args [out]`,
        `u` |-> `update_var out w s`]) >>
     simp[mk_inst_def] >> disch_then irule >> gvs[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspecl_then [`[]`,
    `OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx)`,
    `step_prov PG G (mk_inst sa.cs_next_id opc args [out]) (update_var out w s)`,
    `step_taint (mk_inst sa.cs_next_id opc args [out]) s (update_var out w s) tn`] mp_tac) >>
  simp[] >> impl_tac
  >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[update_var_def]) >>
  gvs[ADD1]
QED

(* Safety of one concrete generated instruction, checked at its input state. *)
Definition array_length_step_ok_def:
  array_length_step_ok lo ctx func opc args w sa out sb s G tn <=>
    emit_op opc args sa = (Var out,sb) /\
    step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
      OK (update_var out w s) /\
    access_ok lo G func (mk_inst sa.cs_next_id opc args [out]) s /\
    taint_ok func tn (mk_inst sa.cs_next_id opc args [out]) s /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    inst_mem_below_frontier (mk_inst sa.cs_next_id opc args [out]) s /\
    inst_dload_in_section (mk_inst sa.cs_next_id opc args [out]) s
End

(* Cursor changes and fresh-register writes are the only runtime effects. *)
Definition array_length_frame_def:
  array_length_frame sa s G tn t G' tn' <=>
    ((t with vs_inst_idx := s.vs_inst_idx) with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\
      FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
End

Theorem array_length_step_joint[local]:
  array_length_step_ok lo ctx func opc args w sa out sb s G tn /\
  MEM opc [ADD; MLOAD; SLOAD; TLOAD; CALLDATALOAD; ILOAD; DLOAD] /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  let i = mk_inst sa.cs_next_id opc args [out];
      u = update_var out w s;
      t = u with vs_inst_idx := LENGTH sb.cs_current_insts;
      G' = step_prov PG G i u;
      tn' = step_taint i s u tn in
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
    eval_operand (Var out) t = SOME w /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    array_length_frame sa s G tn t G' tn'
Proof
  pure_rewrite_tac[LET_THM] >> strip_tac >>
  `opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc` by
    (gvs[] >> simp[is_terminator_def]) >>
  qpat_x_assum `array_length_step_ok _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [array_length_step_ok_def] >> strip_tac >>
  drule_all array_length_emit_concrete >>
  disch_then (qspecl_then [`explicit`, `PG`, `D`] assume_tac) >>
  drule array_length_read_ghost_frame >> disch_then assume_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[array_length_frame_def, eval_operand_def, lookup_var_update_var,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       venom_state_component_equality] >>
  metis_tac[]
QED
