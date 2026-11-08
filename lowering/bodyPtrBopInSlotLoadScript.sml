(* Positioned runtime slot loads, shared by storage and transient backends. *)
Theory bodyPtrBopInSlotLoad
Ancestors bodyPtrBopInBaseBoundary bodyPtrBopInElementLoad bodyPtrBopInLiveStorage bodyPtrBopInSlotContents
  stmtAppendStorageRunPtr venomExecSemantics venomInst venomState exprSimUnwrap
  ptrSafeRun ptrDiscipline fragGasSeqPtr fragGasPathPtr finite_map arithmetic vyperValue

Theorem membership_positioned_slot_load_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) /\
  eval_operand arr_op s = SOME w /\ op_taint tn arr_op = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {} ==>
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out (if tr then tload w s else sload w s) s
        with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) s =
    OK (update_var out (if tr then tload w s else sload w s) s)` by
    (irule (cj 1 membership_slot_header_operand_step) >> simp[] >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) s` by
    (irule (cj 2 membership_slot_header_operand_step) >> simp[] >> metis_tac[]) >>
  `~is_terminator (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]).inst_opcode /\
   (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]).inst_opcode <> INVOKE` by
    (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  drule_all straight_line_ptr_edge >>
  disch_then (qspec_then `PG` mp_tac) >> strip_tac >>
  `step_taint (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) s
     (update_var out (if tr then tload w s else sload w s) s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (irule scalar_storage_load_taint >> simp[eval_operand_def, update_var_def]) >>
  qexists_tac `step_prov PG G
    (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out])
    (update_var out (if tr then tload w s else sload w s) s)` >>
  Cases_on `tr` >>
  simp[bodyPtrBopInLoadOutputTheory.scalar_load_output_prov, scalar_step_old_prov] >>
  gvs[mk_inst_def] >> drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> simp[update_var_def, cj 1 gas_path_ptr_rules]
QED

Theorem membership_frame_slot_state:
  membership_loop_frame sa G0 tn0 s0 G tn s ==>
  s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
  s.vs_call_ctx = s0.vs_call_ctx /\ tn.t_stor = tn0.t_stor /\
  tn.t_trans = tn0.t_trans /\
  (!key. sload key s = sload key s0 /\ tload key s = tload key s0)
Proof
  simp[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >> strip_tac >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >>
  simp[sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem membership_frame_located_slot_ptr_ok:
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G0 tn0 s0 ==>
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s
Proof
  strip_tac >>
  drule_all bodyPtrBopInLoopContractTheory.membership_loop_frame_operand >> strip_tac >>
  drule membership_frame_slot_state >> strip_tac >>
  Cases_on `tr` >> gvs[bodyPtrDefsTheory.ptr_vv_ok_def]
QED

Theorem membership_positioned_slot_load_framed_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) /\
  eval_operand arr_op s = SOME w /\ op_taint tn arr_op = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {} /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  out = "%" ++ toString (sa.cs_next_var+k) /\ 1 < k ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var out (if tr then tload w s else sload w s) s
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    FLOOKUP G' out = NONE /\ op_taint tn' (Var out) = {}
Proof
  strip_tac >> drule_all membership_positioned_slot_load_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  qexists_tac `tn with t_var := tn.t_var |+ (out,{})` >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> reverse conj_tac
  >- (irule membership_registers_scalar_update >> simp[] >>
      qexistsl_tac [`G`, `tn`] >> simp[op_taint_def, FLOOKUP_UPDATE]) >>
  irule membership_frame_scalar_update >>
  conj_tac >- simp[compileEnvTheory.not_fresh_at_def] >>
  qexistsl_tac [`G`, `tn`] >> simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem membership_located_word_array_key_clean:
  storage_holds cx tr aty tvv bw es s /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME bw /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  i < cap /\
  ((bd = Fixed cap /\ prefix = 0) \/
   (bd = Dynamic cap /\ prefix = 1 /\
    i < w2n (lookup_storage bw
      (if tr then s.vs_transient s.vs_call_ctx.cc_address
       else (s.vs_accounts s.vs_call_ctx.cc_address).storage)))) ==>
  w2n (bw + n2w (prefix+i)) = w2n bw + prefix+i /\
  key_taint (if tr then tn.t_trans else tn.t_stor) (bw+n2w (prefix+i)) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  `w2n bw + type_slot_size (ArrayTV tv bd) <= dimword(:256)` by
    metis_tac[bodyPtrBopInRepresentationTheory.membership_storage_extent] >>
  `prefix+i < type_slot_size (ArrayTV tv bd)` by
    (gvs[type_slot_size_def] >> decide_tac) >>
  `prefix+i < dimword(:256) /\ w2n bw + (prefix+i) < dimword(:256)` by decide_tac >>
  `w2n (bw+n2w (prefix+i)) = w2n bw + (prefix+i)` by
    simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, LESS_MOD] >>
  conj_tac >- (asm_rewrite_tac[] >> decide_tac) >>
  `!st bs j b. ~dead_bytes st bs tv j b` by metis_tac[evaluated_word_deadless] >>
  qpat_x_assum `(bd = Fixed _ /\ _) \/ _` strip_assume_tac
  >- (irule located_fixed_deadless_clean >>
      qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> gvs[] >> decide_tac) >>
  irule located_dynamic_element_clean >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexists_tac `i` >>
  fs[sload_def, tload_def, contract_storage_def, contract_transient_def] >>
  gvs[] >> Cases_on `tr` >> gvs[]
QED

Theorem membership_slot_load_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\ s.vs_inst_idx = 2+delta /\
  src = "%" ++ toString (sa.cs_next_var+4+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) /\
  lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {} ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (if tr then tload w s else sload w s) s
      with vs_inst_idx := 3+delta) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_compiled_runtime_address_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+8+delta) (if tr then TLOAD else SLOAD)
      [Var src] [dst])` by (Cases_on `tr` >> gvs[]) >>
  drule_at (Pat `get_instruction _ _ = _`) membership_positioned_slot_load_framed_path >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ _ _ _`)) >>
  gvs[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> fs[ADD1]
QED

Theorem membership_contract_storage_direct:
  contract_storage s = (s.vs_accounts s.vs_call_ctx.cc_address).storage
Proof
  simp[contract_storage_def, vfmStateTheory.lookup_account_def]
QED

Theorem membership_storage_array_key_clean:
  storage_holds cx tr (ArrayT ety bd) tvv bw es s /\
  ptr_vv_ok cx (ArrayT ety bd) tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  i < array_length (ArrayTV tv bd) av /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 1) ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) (bw+n2w (prefix+i)) = {}
Proof
  rpt strip_tac >> drule_all membership_storage_array_bounds >> strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ety bd) = SOME (ArrayTV tv bd)` by
    (fs[loweringPostsTheory.storage_holds_def, evaluate_type_def]) >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  Cases_on `bd` >> gvs[]
  >- (irule (SRULE [] (Q.INST [`prefix` |-> `0`] (cj 2 membership_located_word_array_key_clean))) >>
      qpat_assum `storage_holds _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> qexists_tac `ety` >> simp[]) >>
  drule_all membership_storage_array_length >> strip_tac >>
  `array_length (ArrayTV tv (Dynamic n)) av < dimword(:256)` by
    (drule bodyPtrBopInRepresentationTheory.membership_storage_extent >>
     simp[evaluate_type_def, type_slot_size_def] >>
     strip_tac >> decide_tac) >>
  irule (SIMP_RULE (srw_ss() ++ ARITH_ss) []
    (Q.INST [`prefix` |-> `1`] (cj 2 membership_located_word_array_key_clean))) >>
  qpat_assum `storage_holds _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> qexists_tac `ety` >> simp[] >>
  Cases_on `tr` >>
  gvs[tload_def, sload_def, contract_transient_def,
    membership_contract_storage_direct, wordsTheory.w2n_n2w, LESS_MOD] >> decide_tac
QED

Theorem membership_slot_array_read:
  storage_holds cx tr (ArrayT ety bd) tvv bw es s0 /\
  ptr_vv_ok cx (ArrayT ety bd) tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s0 = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 1) /\
  membership_loop_frame sa G0 tn0 s0 G tn t ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) (bw+n2w (prefix+i)) = {} /\
  (if tr then tload (bw+n2w (prefix+i)) t else sload (bw+n2w (prefix+i)) t) =
    typed_val_to_w256 tv v
Proof
  strip_tac >> drule_all membership_storage_array_key_clean >> strip_tac >>
  drule_all membership_storage_array_load >> strip_tac >>
  drule membership_frame_slot_state >> strip_tac >> Cases_on `tr` >> gvs[]
QED

Theorem membership_slot_array_element_prefix:
  compile_array_membership_loop needle arr_op len 1 prefix
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  storage_holds cx tr (ArrayT ety bd) tvv bw es s0 /\
  ptr_vv_ok cx (ArrayT ety bd) tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s0 = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 1) /\
  delta = (if 0 < prefix then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+5+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (typed_val_to_w256 tv v) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `op_taint tn0 arr_op = {}` by
    (fs[bodyPtrDefsTheory.ptr_vv_ok_def] >> metis_tac[]) >>
  drule (SRULE [] (GEN_ALL membership_runtime_address_prefix)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `q` strip_assume_tac)))) >>
  drule_at (Pat `membership_loop_frame _ _ _ _ G1 tn1 q`)
    (SIMP_RULE (srw_ss() ++ ARITH_ss) [] (GEN_ALL membership_slot_array_read)) >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  fs[] >> disch_then drule_all >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_slot_load_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ G1 tn1 q`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ G1 tn1 q`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G2 tn2 t` >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[update_var_def]
QED
