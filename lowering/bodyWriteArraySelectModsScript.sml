Theory bodyWriteArraySelectMods
Ancestors
  bodyWriteArrayPacketMods bodyFullTargetArrayLoad bodyFullTargetArraySuffix
  fragGasOriginPtrDead fragGasOriginPtrLoop fragFuelExprHelpers fragFuel
  targetSubscriptContinuation exprSimArrayIndex exprLoweringProps freshWrites
  emitHelperProps emitHelper fragExec compileEnv context venomInst venomState
  ptrDiscipline loweringStateRelDefs stmtReasonLitFragMemory finite_map rich_list list words

Theorem write_array_bounds_code[local]:
  array_bounds_check idx len sgn sa = ((),sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)
Proof
  simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
  simp[array_bounds_valid_def, comp_bind_def] >>
  Cases_on `sgn` >> simp[comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND2, APPEND_ASSOC,
       mk_inst_def, is_terminator_def]
QED

Theorem write_array_address_code[local]:
  array_elem_ptr bop idx dyn ws esz sa = (p,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)
Proof
  Cases_on `dyn` >> simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
  gvs[same_blocks_def] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND2, APPEND_ASSOC,
       mk_inst_def, is_terminator_def]
QED

Theorem write_array_length_code[local]:
  (if dyn then compile_ptr_load ctor imm loc bop
   else comp_return (Lit (n2w cnt))) sn = (len,sl) ==>
  ci_mono sn sl /\ same_blocks sn sl /\
  sl.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sl /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sn sl) /\
  (!x. len = Var x ==> not_fresh_at sl x)
Proof
  Cases_on `dyn`
  >- (simp[] >> strip_tac >>
      drule_then assume_tac compile_ptr_load_same_blocks >>
      drule_then assume_tac compile_ptr_load_var >>
      `ci_mono sn sl` by metis_tac[ci_mono_compile_ptr_load, pairTheory.SND] >>
      `!x. len = Var x ==> not_fresh_at sl x` by fs[not_fresh_at_def, var_below_def] >>
      simp[] >> qpat_x_assum `compile_ptr_load _ _ _ _ _ = _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      Cases_on `loc` >> simp[compile_ptr_load_def] >>
      TRY (qmatch_goalsub_rename_tac `compile_imm_load_word ctor imm bop sn` >>
           Cases_on `ctor` >> Cases_on `imm` >> simp[compile_imm_load_word_def]) >>
      simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
           fresh_id_def, emit_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      simp[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  simp[comp_return_def] >> strip_tac >>
  gvs[ci_mono_def, cs_extends_def, same_blocks_def, emitted_insts_def]
QED

(* Expose the actual loader cut for the location-specific read proofs. *)
Theorem write_array_select_cut_mods:
  FST (SND rb) = SOME loc /\ SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  target_subscript_suffix cenv e rb iop sn = (r,sb) ==>
  ?len sl sc.
    (if (case bd of Dynamic _ => T | _ => F) then
       compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST rb)
     else comp_return (Lit (n2w (case bd of Fixed n => n | _ => 0)))) sn = (len,sl) /\
    array_bounds_check iop len (is_signed_type (expr_type e)) sl = ((),sc) /\
    array_elem_ptr (FST rb) iop (case bd of Dynamic _ => T | _ => F)
      (word_scale loc) (elem_size_in_location cenv loc et) sc = (FST r,sb) /\
    r = (FST r,SOME loc,SOME (ValPT et))
Proof
  PairCases_on `rb` >> simp[] >> strip_tac >> gvs[target_subscript_suffix_array] >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sl = (unit,sc)` >>
  Cases_on `unit` >> metis_tac[]
QED

Theorem write_array_loader_unique[local]:
  array_length_loader_ok ctor imm loc bop w sa p sb lo ctx func PG s G tn t1 G1 tn1 /\
  array_length_loader_ok ctor imm loc bop w sa p sb lo ctx func PG s G tn t2 G2 tn2 ==>
  t1 = t2 /\ G1 = G2 /\ tn1 = tn2
Proof
  Cases_on `loc = LocCode /\ ctor /\ IS_SOME imm` >>
  simp[array_length_loader_ok_def, LET_THM] >> rpt strip_tac >>
  gvs[array_length_step_ok_def] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, comp_return_def, emit_def, mk_inst_def] >>
  fs[FUN_EQ_THM] >>
  rpt (qpat_x_assum `!x. _ = _` (qspec_then `sa` mp_tac)) >>
  simp[comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def, compile_state_component_equality,
       instruction_component_equality]
QED

(* Use the concrete loader chosen by the current array view. Its ghost
   values are fixed independently of the dead-byte horizon. *)
Theorem write_array_length_select[local]:
  (if dyn then compile_ptr_load ctor imm loc bop
   else comp_return (Lit (n2w cnt))) sn = (len,sl) /\
  fn_has_code sn sl func /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (~dyn ==> nw = n2w cnt) /\
  (dyn ==> ?ul Gl tl.
    array_length_loader_ok ctor imm loc bop nw sn len sl lo ctx func PG s G tn ul Gl tl /\
    op_prov Gl len = NONE /\ op_taint tl len = {}) ==>
  ?ul Gl tl.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK ul,Gl,tl)) /\
    eval_operand len ul = SOME nw /\ op_prov Gl len = NONE /\ op_taint tl len = {} /\
    ~ul.vs_halted /\ ul.vs_current_bb = sl.cs_current_bb /\
    ul.vs_inst_idx = LENGTH sl.cs_current_insts /\ array_length_frame sn s G tn ul Gl tl
Proof
  strip_tac >>
  `(dyn ==> ?ul Gl tl.
    array_length_loader_ok ctor imm loc bop nw sn len sl lo ctx func PG s G tn ul Gl tl)` by
    (strip_tac >> first_x_assum drule >> strip_tac >> metis_tac[]) >>
  drule_all array_length_joint >>
  disch_then (qspecl_then [`explicit`,
    `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`]
    strip_assume_tac) >>
  qexistsl [`t`,`G'`,`tn'`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_from_no_dead >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `dyn`)
  >- gvs[comp_return_def, op_prov_def, op_taint_def] >>
  gvs[] >> metis_tac[write_array_loader_unique]
QED

Theorem write_array_length_operand[local]:
  array_length_frame sa s G tn t G' tn' /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  eval_operand op t = eval_operand op s /\
  op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op
Proof
  Cases_on `op` >> simp[array_length_frame_def, eval_operand_def, op_taint_def, op_prov_def] >>
  strip_tac >> gvs[venom_state_component_equality]
QED

Theorem write_array_length_allocas[local]:
  array_length_frame sn s G tn ul Gl tl /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  allocas_from lo ul /\ (ctx_has_dalloca ctx ==> allocas_below_fmp ul)
Proof
  strip_tac >>
  qpat_x_assum `array_length_frame _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE [] o
     Q.AP_TERM `\st. (st.vs_allocas,st.vs_initial_fmp,st.vs_fmp)` o
     cj 1 o REWRITE_RULE [array_length_frame_def]) >>
  conj_tac
  >- (qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  qpat_x_assum `ctx_has_dalloca ctx ==> _` mp_tac >> simp[allocas_below_fmp_def] >>
  metis_tac[]
QED

Theorem write_array_compose_frame[local]:
  array_length_frame sn s G tn ul Gl tl /\ sn.cs_next_var <= sl.cs_next_var /\
  (!x. not_fresh_at sl x ==>
    FLOOKUP H x = FLOOKUP Gl x /\ FLOOKUP tm.t_var x = FLOOKUP tl.t_var x /\
    FLOOKUP q.vs_vars x = FLOOKUP ul.vs_vars x) /\
  (q with <|vs_vars := ul.vs_vars; vs_inst_idx := ul.vs_inst_idx|>) =
    (if ok then ul else revert_state (set_returndata [] ul)) ==>
  (!x. not_fresh_at sn x ==>
    FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
    FLOOKUP q.vs_vars x = FLOOKUP s.vs_vars x) /\
  (q with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) =
    (if ok then s else revert_state (set_returndata [] s))
Proof
  simp[array_length_frame_def, lookup_var_def] >> strip_tac >> conj_tac
  >- (rpt strip_tac >> `not_fresh_at sl x` by metis_tac[not_fresh_at_mono] >>
      qpat_assum `!x. not_fresh_at sn x ==> _` drule >>
      qpat_assum `!x. not_fresh_at sl x ==> _` drule >> simp[]) >>
  qpat_x_assum `q with <|vs_vars := _; vs_inst_idx := _|> = _` mp_tac >>
  qpat_x_assum `(ul with vs_inst_idx := _) with vs_vars := _ = _` mp_tac >>
  Cases_on `ok` >>
  simp[venom_state_component_equality, revert_state_def, set_returndata_def] >>
  strip_tac >> fs[]
QED

(* A suffix run starts at the actual post-index machine state. Only the
   dynamic case asks the caller to certify a load of the current header. *)
Theorem write_array_select_run_mods:
  FST (SND rb) = SOME loc /\ SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  target_subscript_suffix cenv e rb iop sn = (r,sb) /\ fn_has_code sn sb func /\
  eval_operand (FST rb) t2 = SOME b /\ eval_operand iop t2 = SOME iw /\
  (!x. FST rb = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  op_taint tn2 (FST rb) = {} /\ op_taint tn2 iop = {} /\ op_prov G2 iop = NONE /\
  allocas_from lo t2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
  ~t2.vs_halted /\ t2.vs_current_bb = sn.cs_current_bb /\
  t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!n. bd = Fixed n ==> nw = n2w n) /\
  (!cap len sl. bd = Dynamic cap /\
    compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST rb) sn = (len,sl) ==>
    ?ul Gl tl.
      array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST rb) nw
        sn len sl lo ctx func PG t2 G2 tn2 ul Gl tl /\
      op_prov Gl len = NONE /\ op_taint tl len = {}) ==>
  ?t3 G3 tn3.
    write_array_select_frame
      ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
       (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
       (st0,es,sa,s0,G0,tn0),
       (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
       (base_gas,mid1,pv,t1,G1,tn1),
       (index_gas,mid2,v,t2,G2,tn2))
      (loc,b,iw,nw) (t3,G3,tn3)
Proof
  strip_tac >> drule_all_then strip_assume_tac write_array_select_cut_mods >>
  drule_then strip_assume_tac write_array_bounds_code >>
  drule_then strip_assume_tac write_array_address_code >>
  drule_then strip_assume_tac write_array_length_code >>
  `cs_extends sn sl /\ cs_extends sl sc /\ cs_extends sc sb` by
    fs[ci_mono_def, cs_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
  `cs_extends sl sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sn sl func /\ fn_has_code sl sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sl sc func /\ fn_has_code sc sb func` by metis_tac[fn_has_code_split] >>
  `emitted_insts sn sc = emitted_insts sn sl ++ emitted_insts sl sc` by
    metis_tac[emitted_insts_append] >>
  `sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc` by simp[APPEND_ASSOC] >>
  `emitted_insts sn sb = emitted_insts sn sc ++ emitted_insts sc sb` by
    metis_tac[emitted_insts_append] >>
  `sb.cs_current_bb = sn.cs_current_bb /\
   sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sn sb)` by
    fs[same_blocks_def, EVERY_APPEND, APPEND_ASSOC] >>
  `?ul Gl tl.
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t2,G2,tn2) [] (OK ul,Gl,tl)) /\
    eval_operand len ul = SOME nw /\ op_prov Gl len = NONE /\ op_taint tl len = {} /\
    ~ul.vs_halted /\ ul.vs_current_bb = sl.cs_current_bb /\
    ul.vs_inst_idx = LENGTH sl.cs_current_insts /\ array_length_frame sn t2 G2 tn2 ul Gl tl` by
    (irule write_array_length_select >> simp[] >>
     qexistsl [`FST rb`,`case bd of Fixed n => n | _ => 0`,
               `cenv.ce_is_ctor`,`case bd of Dynamic _ => T | _ => F`,
               `cenv.ce_imm_alloca`,`loc`] >>
     simp[] >> Cases_on `bd` >> fs[] >> qexistsl [`ul`,`Gl`,`tl`] >> simp[]) >>
  `sn.cs_next_var <= sl.cs_next_var` by fs[ci_mono_def] >>
  `(!x. FST rb = Var x ==> not_fresh_at sl x) /\
   (!x. iop = Var x ==> not_fresh_at sl x)` by metis_tac[not_fresh_at_mono] >>
  `eval_operand (FST rb) ul = SOME b /\ eval_operand iop ul = SOME iw /\
   op_prov Gl (FST rb) = op_prov G2 (FST rb) /\ op_prov Gl iop = NONE /\
   op_taint tl (FST rb) = {} /\ op_taint tl iop = {}` by
    (drule write_array_length_operand >>
     disch_then (fn step =>
       qspec_then `FST rb` mp_tac step >> qspec_then `iop` mp_tac step) >> simp[]) >>
  drule_all_then strip_assume_tac write_array_length_allocas >>
  drule_all array_tail_scalar_uniform >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`t3`,`G3`,`tn3`] strip_assume_tac)) >>
  drule_all_then strip_assume_tac write_array_compose_frame >>
  qexistsl [`t3`,`G3`,`tn3`] >>
  simp[write_array_select_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gl`,`ul`,`tl`] >> simp[]) >>
  qpat_x_assum `array_length_frame _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_length_frame_def]) >>
  simp[] >> strip_tac >> qexists_tac `emitted_insts sn sb` >> simp[]
QED
