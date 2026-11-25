(* The constructor Len load reads the staged header, with or without
   an ADD of the immutable base. Neither path changes memory or allocas. *)
Theory bodyLenCtorCodeRunMods
Ancestors
  bodyFullPostsMods augAssignFullImmutableValidLoad bodyBinopFragMemory
  bodyPtrBopInRepresentation bodyFullHashKeccakFixed representationCleanPtr
  stmtReasonLitFragMemory exprLoweringProps exprSimCopy stateFrame
  builtinSimple context ptrDiscipline bodyPtrDefs bodyFullShadowBodyInv
  loweringStateRelDefs venomState venomInst fragGasOriginPtr valueEncodingDefs
  words arithmetic list finite_map pred_set

Theorem len_ctor_ib_ready[local]:
  stmt_state_rel H ctx func cenv cx ee t /\
  ghost_inv_at_mods DH lo d cenv cx ee G tn t /\
  local_ptrs_reserved cenv sm /\ lo <> 0 /\ cenv.ce_imm_alloca = SOME ib ==>
  eval_operand ib t = SOME 0w /\ copy_old_operand sm ib /\
  op_taint tn ib = {} /\ op_prov G ib = NONE
Proof
  strip_tac >> drule_all_then assume_tac membership_immutable_base_value >>
  Cases_on `ib` >> fs[copy_old_operand_def,op_taint_def,op_prov_def] >>
  drule_all_then assume_tac local_ptrs_reserved_imm_base >>
  fs[ghost_inv_at_mods_def,op_taint_def]
QED

Theorem len_ctor_header_clean[local]:
  (!m. mem_agree_outside dirty mem m ==> mem_word_at a m = w) ==>
  mem_word_taint dirty a = {}
Proof
  strip_tac >> drule robust_mem_word_at_clean >> strip_tac >>
  simp[mem_word_taint_def,EXTENSION] >> gen_tac >> Cases_on `x < 32` >> simp[] >>
  first_x_assum irule >> decide_tac
QED

Theorem len_ctor_slice_history[local]:
  fn_has_code sm sb func /\ sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> ALLOCA) code /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  z.vs_current_bb = t.vs_current_bb /\ z.vs_allocas = t.vs_allocas /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t ==>
  alloca_history func z
Proof
  strip_tac >> drule_all_then strip_assume_tac fn_has_code_code >>
  fs[rich_listTheory.IS_PREFIX_APPEND] >>
  `z.vs_inst_idx = t.vs_inst_idx + LENGTH code` by simp[] >>
  `alloca_history func (z with vs_inst_idx := t.vs_inst_idx + LENGTH code)` by
    (irule alloca_history_no_alloca_slice >> simp[] >>
     qexistsl [`bb`,`l`,`t`] >> simp[]) >>
  qpat_x_assum `alloca_history func (z with vs_inst_idx := _)` mp_tac >>
  qpat_assum `z.vs_inst_idx = _`
    (fn th => pure_rewrite_tac[GSYM th,venom_state_fupdselfid]) >> simp[]
QED

Theorem len_ctor_code_run_mods:
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
    (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  copy_old_operand sm (vv_operand vv) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
  ghost_inv_at_mods DH lo d cenv cx ee G tn t /\
  eval_operand (vv_operand vv) t = SOME w /\ w2n w + 32 <= lo /\
  mload (w2n w) t = n2w n /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> mem_word_at (w2n w) m = n2w n) ==>
  ?z G2 tn2.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2)) /\
    eval_operand op z = SOME (n2w n) /\ op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (alloca_history func t ==> alloca_history func z) /\
    z = t with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x t /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee t` by fs[vv_post_mods_def] >>
  drule_then assume_tac (SPEC_ALL stmt_state_rel_allocas_below_fmp) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `op_taint tn (vv_operand vv) = {} /\ op_prov G (vv_operand vv) = NONE` by
    (Cases_on `vv` >> gvs[vv_location_def,vv_operand_def,ptr_vv_ok_def]) >>
  `!ib. cenv.ce_imm_alloca = SOME ib ==>
     eval_operand ib t = SOME 0w /\ copy_old_operand sm ib /\
     op_taint tn ib = {} /\ op_prov G ib = NONE` by
    (rpt strip_tac >> `lo <> 0` by decide_tac >>
     drule_all_then strip_assume_tac len_ctor_ib_ready >> simp[]) >>
  drule_then assume_tac len_ctor_header_clean >>
  `compile_imm_load_word T cenv.ce_imm_alloca (vv_operand vv) sm = (op,sb)` by
    (qpat_x_assum `compile_builtin_len _ _ _ _ _ = _` mp_tac >>
     simp[compile_builtin_len_def,compile_ptr_load_def]) >>
  drule_all augassign_ctor_word_load_at >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `alloca_history func t ==> alloca_history func u` by
    (disch_tac >> irule len_ctor_slice_history >>
     qexistsl [`emitted_insts sm sb`,`sb`,`sm`,`t`] >>
     fs[state_frame_def]) >>
  `u = t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>` by
    fs[state_frame_def,venom_state_component_equality] >>
  `eval_operand op u = SOME (n2w n)` by fs[] >>
  qexistsl [`u`,`G1`,`tn1`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
