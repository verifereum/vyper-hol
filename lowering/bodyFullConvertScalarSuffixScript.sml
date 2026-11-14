Theory bodyFullConvertScalarSuffix
Ancestors
  bodyFullConvertScalarRun bodyFullConvertScalarCertificate bodyFullConvertScalarFrame
  freshWrites stateFrame instIdxIndep
  exprSimConvert exprSimConvertFromBytes bodyPtrTypeBuiltinsScalarChecks
  bodyPtrTypeBuiltinsScalarArithmetic convertScalarFlags
  gasOutcomeFullCompose bodyFullPreds loweringPosts exprSimDefs
  exprLoweringProps fragGasSeqPtr fragGasOriginPtr vyperAST venomState

Theorem zero_convert_full_outcome:
  is_bytestring_type src /\ is_word_type dst /\
  valid_conversion src dst /\ well_formed_type (get_tenv cx) dst /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  (v = BytesV [] \/ v = StringV []) /\ ~s.vs_halted ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (\st. (convert_result cx src dst v,st)) (ee,s,G,tn)
    (\H res fin Gf tnf t. ?vout dtv.
      res = INL vout /\ evaluate_type (get_tenv cx) dst = SOME dtv /\
      typed_val_to_w256 dtv vout = 0w /\
      fin = ee with gas_obs := [] /\ t = s /\ Gf = G /\ tnf = tn) R
Proof
  strip_tac >>
  `~is_bytestring_type dst` by metis_tac[is_word_type_not_bytestring] >>
  `?vout dtv. convert_result cx src dst v = INL vout /\
    evaluate_type (get_tenv cx) dst = SOME dtv /\
    typed_val_to_w256 dtv vout = 0w` by
    metis_tac[dynamic_empty_scalar_convert] >>
  irule gas_outcome_full_pure >>
  simp[] >> qexistsl_tac [`G`,`ee`,`INL vout`,`s`,`tn`] >>
  simp[gas_origin_ptr_path_rules] >> metis_tac[]
QED

Theorem zero_convert_child_post:
  expr_post H ctx func cenv cx e es sa s1 s0 ee v1 x s /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  typed_val_to_w256 tv v = 0w ==>
  expr_post H ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa s1 s0
    ee v (Lit 0w) s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def] >> metis_tac[]
QED

(* Physical and ghost endpoints are selected before any dead mask. *)
Theorem scalar_convert_origin_path:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ fresh_vars_wrt sa s /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ((!vout. convert_result cx src dst v = INL vout ==>
    ?dtv t Gf tnf.
      evaluate_type (get_tenv cx) dst = SOME dtv /\ value_has_type dtv vout /\
      eval_operand out t = SOME (typed_val_to_w256 dtv vout) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
      state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!z. not_fresh_at sa z ==>
        lookup_var z t = lookup_var z s /\ FLOOKUP Gf z = FLOOKUP G z /\
        op_taint tnf (Var z) = op_taint tn (Var z)) /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      op_prov Gf out = NONE /\ op_taint tnf out = {}) /\
   (!exc. convert_result cx src dst v = INR exc ==>
    (?msg. exc = Error (RuntimeError msg)) /\
    ?err t Gf tnf.
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (Abort err t,Gf,tnf)))
Proof
  strip_tac >> drule_all scalar_convert_typed_run >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!vout. _` drule >> strip_tac >>
      drule_at (Pat `run_inst_seq _ _ = _`) scalar_convert_run_origin >>
      disch_then (drule_all o SRULE []) >>
      disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
      drule_all scalar_convert_straight >>
      disch_then (qspecl_then [`x`,`cenv`] (mp_tac o SRULE [straight_fresh_def])) >>
      disch_then drule >> strip_tac >>
      qexistsl_tac [`dtv`,`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`H`,`th`] >>
      gvs[exec_result_map_def, eval_operand_def, lookup_var_def,
          state_frame_def, venom_state_component_equality] >> metis_tac[]) >>
  gen_tac >> disch_tac >> qpat_x_assum `!exc. _` drule >> strip_tac >>
  conj_tac >- metis_tac[] >>
  drule_at (Pat `run_inst_seq _ _ = _`) scalar_convert_run_origin >>
  disch_then (drule_all o SRULE []) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`err`,`t with vs_inst_idx := j`,`H`,`th`] >>
  fs[exec_result_map_def]
QED

Theorem scalar_convert_endpoint_posts:
  expr_post H ctx func cenv cx e es sa s1 s0 ee v1 x t0 /\
  ghost_inv_at D lo d cenv cx ee G tn t0 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  storage_well_formed_on cx ee (FST H) /\
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tv /\
  value_has_type tv v /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  local_ptrs_reserved cenv s1 /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at s1 z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
          not_fresh_at s1 z) /\
  sa.cs_next_var <= s1.cs_next_var /\
  state_frame s = state_frame (t0 with vs_inst_idx := s.vs_inst_idx) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!z. not_fresh_at s1 z ==>
       lookup_var z s = lookup_var z t0 /\
       FLOOKUP Gf z = FLOOKUP G z /\
       op_taint tnf (Var z) = op_taint tn (Var z)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  op_taint tnf op = {} /\ op_prov Gf op = NONE ==>
  expr_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee v op s /\
  ghost_inv_at D lo d cenv cx ee Gf tnf s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf /\
  storage_well_formed_on cx ee (FST H) /\
  ptr_val_ok cx typ v op Gf tnf s /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  MATCH_ACCEPT_TAC scalar_convert_endpoint_frames
QED
