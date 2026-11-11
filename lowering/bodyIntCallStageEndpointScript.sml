(* One counted endpoint for all aligned staged arguments. *)
Theory bodyIntCallStageEndpoint
Ancestors
  bodyIntCallStageList bodyIntCallStageOwned bodyIntCallStageTransport
  bodyIntCallHeldArgs exprSimWordArgs exprLoweringProps fragGasFocus
  context exprLowering compileEnv

Theorem intcall_stage_args_endpoint:
  !H flags sm sn ops a s.
  compile_stage_intcall_args ce (MAP (\(ty,raw,vv). vv) H) flags
    (MAP (\(ty,raw,vv). ty) H) sm = (ops,sn) /\
  LENGTH flags = LENGTH H /\
  EVERY (\(ty,raw,vv). vv_type vv = ty /\
    type_memory_bytes ce ty < dimword(:256) /\
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
         type_memory_bytes ce ty = type_memory_size tv) H /\
  LIST_REL (\(ty,raw,vv) flag. flag ==> is_word_type ty) H flags /\
  intcall_held_args ce cx a sm es s H /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sm sn func /\ local_ptrs_reserved ce sm /\
  expr_sim_inv ce cx env es /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  (!aid. sm.cs_next_id <= aid ==> aid NOTIN FDOM s.vs_allocas) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t D. gas_marked_path F ctx func s 0 (OK t) /\
    EVERY (staged_arg ce func es sm sn t) D /\
    MAP (\(ty,tv,v,flag,op). op) D = ops /\
    LIST_REL (\((ty,raw,vv),flag) (ty',tv,v,flag',op).
      ty' = ty /\ flag' = flag /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      read_result cx raw es = (INL v,es)) (ZIP(H,flags)) D /\
    stmt_state_rel ctx func ce cx es t /\ wb_frame ce es sm s t /\
    local_ptrs_reserved ce sn /\
    (!aid. sn.cs_next_id <= aid ==> aid NOTIN FDOM t.vs_allocas) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  Induct >> rpt gen_tac
  >- (simp[] >> strip_tac >>
      gvs[compile_stage_intcall_args_def, comp_return_def] >>
      qexists_tac `s` >> simp[wb_frame_refl,
        fragGasModeTheory.gas_marked_path_def] >>
      metis_tac[fragGasPathTheory.gas_path_rules]) >>
  PairCases_on `h` >> Cases_on `flags` >> simp[] >>
  strip_tac >>
  rename1 `intcall_held_args ce cx a sm es s ((ty,raw,vv)::H)` >>
  rename1 `compile_stage_intcall_args ce (vv::vals) (flag::flags) (ty::tys) sm = (ops,sn)` >>
  Cases_on `flag` >> gvs[]
  >- suspend "word"
  >> suspend "memory"
QED

Resume intcall_stage_args_endpoint[word]:
  drule intcall_stage_word_parts >> strip_tac >>
  drule_all intcall_stage_word_code >> strip_tac >>
  `sm.cs_next_id NOTIN FDOM s.vs_allocas` by simp[] >>
  drule (SRULE [] intcall_stage_word_owned) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `!aid. sm'.cs_next_id <= aid ==> aid NOTIN FDOM z.vs_allocas` by
    (gvs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `!flags' sm' sn' ops' a' s''. _`
    (qspecl_then [`flags`,`sm'`,`sn`,`rest`,`a`,`z`] mp_tac) >>
  simp[] >> strip_tac >>
  `staged_arg ce func es sm sn t (vv_type vv,tv,v,T,op)` by
    (qpat_assum `staged_arg _ _ _ sm sm' z _`
       (mp_then Any mp_tac staged_arg_path_transport) >>
     simp[] >> disch_then irule >>
     gvs[ci_mono_def] >> qexistsl_tac [`ctx`,`cx`,`F`,`0`] >> simp[]) >>
  `EVERY (staged_arg ce func es sm sn t) D` by
    (irule staged_args_lower_frontier >> goal_assum (drule_at Any) >>
     gvs[ci_mono_def]) >>
  `wb_frame ce es sm s t` by
    (irule exprSimConvertBytesTheory.convert_wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`z`,`sm'`] >> gvs[ci_mono_def]) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl_tac [`t`,`(vv_type vv,tv,v,T,op)::D`] >> simp[] >>
  metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0]
QED

Resume intcall_stage_args_endpoint[memory]:
  drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`) intcall_stage_memory_parts >> simp[] >> strip_tac >>
  drule_all intcall_stage_memory_code >> strip_tac >>
  drule (SRULE [] intcall_stage_memory_owned) >> simp[] >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK z)` >>
  `sm.cs_next_id <= sj.cs_next_id` by
    (gvs[ci_mono_def] >> decide_tac) >>
  `!aid. sj.cs_next_id <= aid ==> aid NOTIN FDOM z.vs_allocas` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  qpat_x_assum `!flags' sm' sn' ops' a' s''. _`
    (qspecl_then [`flags`,`sj`,`sn`,`rest`,`a`,`z`] mp_tac) >>
  simp[] >> strip_tac >>
  `staged_arg ce func es sm sn t (vv_type vv,tv,v,F,buf.buf_operand)` by
    (qpat_assum `staged_arg _ _ _ sm sj z _`
       (mp_then Any mp_tac staged_arg_path_transport) >>
     simp[] >> disch_then irule >>
     gvs[ci_mono_def] >> qexistsl_tac [`ctx`,`cx`,`F`,`0`] >> simp[]) >>
  `EVERY (staged_arg ce func es sm sn t) D` by
    (irule staged_args_lower_frontier >> goal_assum (drule_at Any) >> simp[]) >>
  `wb_frame ce es sm s t` by
    (irule exprSimConvertBytesTheory.convert_wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`z`,`sj`] >> gvs[ci_mono_def] >> decide_tac) >>
     qexistsl_tac [`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl_tac [`t`,`(vv_type vv,tv,v,F,buf.buf_operand)::D`] >> simp[] >>
  metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0]
QED

Finalise intcall_stage_args_endpoint
