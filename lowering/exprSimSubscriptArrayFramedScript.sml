(* Length and element-layout boundaries for framed array subscripts. *)
Theory exprSimSubscriptArrayFramed
Ancestors
  exprSimSubscriptArrayFrame exprSimSubscriptArrayOrigin exprSimArrayIndex exprSimLen exprSimCopy
  exprSimSubscriptArraySource vyperState vyperMisc
  exprSimAggregateEncoding exprSimProps loweringPosts vyperTypeSystem arithmetic
  emitHelperProps exprLoweringProps venomExecSemantics exprLowering compileEnv loweringStateRelDefs
  exprSimHypsDefs supportedExprTraverse vyperTypeCallStackSoundness
  freshWrites fragGasFresh moduleLoweringProps venomState exprSimUnopProps
  fragExec fragGasSeq fragGasMode venomInst list rich_list finite_map
Libs
  emitTacticsLib

(* The runtime loader of a code array's length word: a DLOAD of the data
   section at the base. *)
Theorem array_len_ok_DLOAD:
  !imm cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt (compile_ptr_load F imm LocCode) base_op ss
      (word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n b) ss.vs_data_section ++ REPLICATE 32 0w)))
Proof
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def,
     contextTheory.compile_imm_load_word_runtime] >>
  imp_res_tac emit_op_extends >>
  qspecl_then [`DLOAD`, `\a s. word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))`]
    mp_tac emit_op_read1_correct >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  simp[step_inst_base_def, exec_read1_def] >> strip_tac >>
  first_x_assum (qspecl_then [`b`, `ss`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem immutable_array_len_ok:
  stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT et (Dynamic bound)) r w es s /\
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es) r (Type (ArrayT et (Dynamic bound))) /\
  result_array_length cx r es = (INL n,es) /\
  eval_operand base_op s = SOME w ==>
  array_len_ok T cnt (compile_ptr_load F imm LocCode) base_op s (n2w n)
Proof
  strip_tac >> drule_all immutable_holds_data >> strip_tac >>
  `value_has_type tvt v` by gvs[immutable_holds_def] >>
  `mem_word_at (w2n w) s.vs_data_section = n2w n` by
    (irule read_result_memory_header >> simp[is_sized_type_def] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`cx`, `env`, `es`, `r`, `ArrayT et (Dynamic bound)`] >>
     simp[]) >>
  drule array_len_ok_DLOAD >>
  gvs[valueEncodingDefsTheory.mem_word_at_def]
QED

Theorem sub_layout_array_element:
  sub_layout itv iv k (ArrayTV et bd) (ArrayV av) /\
  val_wf (ArrayTV et bd) (ArrayV av) /\
  array_index (ArrayTV et bd) av i = SOME v ==>
  sub_layout itv iv
    (k + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
     Num i * type_memory_size et) et v
Proof
  strip_tac >> Cases_on `av` >> Cases_on `bd` >>
  gvs[valueEncodingDefsTheory.val_wf_def, vyperValueOperationTheory.array_index_def,
      AllCaseEqs(), listTheory.oEL_THM] >>
  gvs[sub_layout_def, valueEncodingTheory.type_memory_size_def]
  >~ [`ArrayV (DynArrayV vs)`]
  >- (`(Num i + 1) * type_memory_size et <= n * type_memory_size et` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      conj_tac
      >- (qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
          pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
      rpt strip_tac >> first_x_assum drule >>
      simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
      drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  (`(Num i + 1) * type_memory_size et <= n * type_memory_size et` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!b mem. _` (qspecl_then [`b`, `mem`] mp_tac) >>
  simp[valueEncodingPropsTheory.val_in_memory_sarray] >> strip_tac >>
  metis_tac[valueEncodingProofsTheory.kvs_in_memory_lookup, ADD_ASSOC])
QED

Theorem local_val_at_array_element:
  local_val_at cenv cx n k (ArrayTV et bd) (ArrayV av) /\
  mem_step_offset (ArrayTV et bd) (ValueSubscript (IntV i)) = SOME (j,et) ==>
  local_val_at cenv cx n (k + j) et v
Proof
  simp[local_val_at_def] >> strip_tac >> disj1_tac >>
  drule_all local_path_at_step >> simp[]
QED

(* Select a typed element within the immutable's represented array. *)
Theorem immutable_holds_array_element:
  immutable_holds cenv cx (ArrayT et bd) r w es s /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  value_has_type etv v /\ read_result cx child es = (INL v,es) ==>
  immutable_holds cenv cx et child
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
              Num i * type_memory_size etv)) es s
Proof
  strip_tac >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  drule_all sub_layout_array_element >> simp[] >> strip_tac >>
  irule immutable_holds_sub >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem vv_at_fixed_array_element:
  vv_at cenv cx (ArrayT et (Fixed n)) sa sb es r (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx child es = (INL v,es) /\ val_wf etv v /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  (!id path'. child = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV i)] /\ r = PlaceR (MemoryPlace id path)) /\
  eval_operand dst s = SOME dw /\ w2n dw = w2n w + j ==>
  vv_at cenv cx et sa sb es child (LocatedValue et (mk_ptr dst LocMemory)) s
Proof
  strip_tac >>
  `val_footprint etv v <= type_memory_size etv` by
    (irule val_footprint_le >> simp[]) >>
  `j + val_footprint etv v <= n * type_memory_size etv` by
    (gvs[mem_step_offset_def, AllCaseEqs()] >>
     `(Num i + 1) * type_memory_size etv <= n * type_memory_size etv` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  `val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) = n * type_memory_size etv` by
    simp[val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def, contextTheory.mk_ptr_def] >> strip_tac >> gvs[]
  >~ [`FLOOKUP s.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n'`, `b`, `sz`] >>
  simp[] >>
  `j + w2n w - b = (w2n w - b) + j` by decide_tac >>
  qpat_x_assum `j + w2n w - b = _` SUBST1_TAC >>
  conj_tac
  >- (drule_all local_val_at_array_element >>
      disch_then (qspec_then `v` ACCEPT_TAC)) >>
  irule exprSimPropsTheory.local_place_at_step >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem vv_holds_array_element:
  vv_holds cenv cx (ArrayT et bd) r (LocatedValue ann p) es s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand s = SOME w /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\ value_has_type etv v /\
  read_result cx child es = (INL v,es) /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst s = SOME (w + n2w j) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) ==>
  vv_holds cenv cx et child (LocatedValue et (mk_ptr dst p.ptr_location)) es s
Proof
  strip_tac >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  drule_all sub_layout_array_element >> simp[] >> strip_tac >>
  gvs[vv_holds_def, contextTheory.mk_ptr_def, is_bytestring_type_def]
  >~ [`p.ptr_location = LocCode`]
  >- (drule_all immutable_holds_array_element >> simp[]) >>
  conj_asm1_tac
  >- (qpat_x_assum `sub_layout _ _ _ etv v` mp_tac >>
      simp[sub_layout_def] >> metis_tac[]) >>
  strip_tac >> irule val_in_memory_word_type >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`et`, `get_tenv cx`] >> simp[]
QED

(* Expose the two child intervals and the bounds/element tail once. *)
Theorem compile_expr_array_subscript:
  compile_expr cenv ty (Subscript ann obj idx) st = (vv, st') /\
  place_type cenv obj = ValPT (ArrayT et bd) ==>
  ?bvv st1 iop st2 dst loc.
    compile_expr cenv ty obj st = (bvv, st1) /\
    lower_value compile_expr cenv ty idx st1 = (iop, st2) /\
    loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location cenv loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc)
      st2 = (dst, st') /\
    vv = LocatedValue ann (mk_ptr dst loc)
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, lower_value_def,
       exprCallBoundsTheory.expr_child_callback_def,
       comp_bind_def, comp_return_def,
       vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED


Theorem straight_fresh_compile_array_subscript:
  (dyn ==> straight_fresh (loader base_op)) ==>
  straight_fresh
    (compile_array_subscript base_op idx_op dyn cnt ws esz sgn loader)
Proof
  strip_tac >> rewrite_tac[compile_array_subscript_split] >>
  irule straight_fresh_bind >> reverse conj_tac
  >- (Cases_on `dyn` >> gvs[straight_fresh_return]) >>
  gen_tac >> BETA_TAC >> irule straight_fresh_array_check_ptr
QED


(* Unlike arithmetic fresh writes, DLOAD reads the actual data section.
   No freshness of the entry variable map is needed for this execution. *)
Theorem compile_imm_load_word_runtime_run:
  compile_imm_load_word F imm base_op sa = (op,sb) /\
  eval_operand base_op s = SOME b ==>
  ?p. op = Var p /\
    p = STRING #"%" (toString sa.cs_next_var) /\
    run_inst_seq (emitted_insts sa sb) s =
      OK (update_var p (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) s)
Proof
  simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_def, exec_read1_def,
       venomInstTheory.mk_inst_def]
QED

Theorem compile_imm_load_word_runtime_frame:
  compile_imm_load_word F imm base_op sa = (Var p,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx es
    ((update_var p w s) with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (!z. not_fresh_at sa z ==>
    lookup_var z ((update_var p w s) with vs_inst_idx := LENGTH sb.cs_current_insts) =
    lookup_var z s)
Proof
  simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `!z. not_fresh_at sa z ==>
    lookup_var z (update_var (STRING #"%" (toString sa.cs_next_var)) w s) =
    lookup_var z s` by
    (rpt strip_tac >> drule lookup_var_update_not_fresh >> simp[]) >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx, update_var_def] >>
      irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
      `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      first_x_assum drule >> simp[lookup_var_def, update_var_def]) >>
  rpt strip_tac >> first_x_assum drule >>
  simp[lookup_var_def, update_var_def]
QED

Theorem compile_imm_load_word_runtime_path:
  compile_imm_load_word F imm base_op sa = (op,sb) /\
  eval_operand base_op s = SOME b /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) /\
    gas_marked_path F ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all compile_imm_load_word_runtime_run >> strip_tac >>
  qexists_tac `update_var p (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) s` >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[DROP_APPEND]) >>
  conj_tac
  >- (drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      simp[gas_marked_path_def, venomInstTheory.mk_inst_def,
           is_terminator_def, is_ext_call_op_def, update_var_def] >>
      gvs[venomInstTheory.mk_inst_def]) >>
  gvs[same_blocks_def]
QED

(* Counted split-tail prototype.  The read is executed on the actual state;
   the arithmetic suffix can still use the clean fresh-variable interface. *)
Theorem runtime_array_split_counted:
  compile_imm_load_word F imm base_op sa = (lop,sm) /\
  comp_ignore_bind (array_bounds_check idx_op lop sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (op,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  eval_operand base_op s = SOME b /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~u.vs_halted /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    (!t0. run_inst_seq (emitted_insts sm sb) (drop_fresh sm u) = OK t0 ==>
      ?t. vars_ext t0 t /\ gas_marked_path F ctx func s 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
    (!a t0. run_inst_seq (emitted_insts sm sb) (drop_fresh sm u) = Abort a t0 ==>
      ?t j. gas_marked_path F ctx func s 0 (Abort a (t with vs_inst_idx := j)))
Proof
  strip_tac >> drule_all compile_imm_load_word_runtime_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  simp[] >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `~(t with vs_inst_idx := LENGTH sm.cs_current_insts).vs_halted /\
   (t with vs_inst_idx := LENGTH sm.cs_current_insts).vs_current_bb = sm.cs_current_bb /\
   (t with vs_inst_idx := LENGTH sm.cs_current_insts).vs_inst_idx = LENGTH sm.cs_current_insts` by simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all straight_fresh_clean_success_path >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      goal_assum (drule_at Any) >>
      drule_all gas_marked_path_then >> simp[]) >>
  rpt strip_tac >> drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t'`, `j`] >> drule_all gas_marked_path_then >> simp[]
QED

Theorem fixed_array_subscript_counted_ok:
  compile_array_subscript base_op idx_op F cnt ws esz sgn loader sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand op t = SOME (b + i * n2w esz) /\
    (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==> lookup_var z t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
  `array_len_ok F cnt loader base_op (drop_fresh sa s) (n2w cnt)` by
    simp[array_len_ok_static] >>
  drule_all compile_array_subscript_ok >> strip_tac >>
  `straight_fresh (compile_array_subscript base_op idx_op F cnt ws esz sgn loader)` by
    simp[straight_fresh_compile_array_subscript] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem fixed_array_subscript_counted_oob:
  compile_array_subscript base_op idx_op F cnt ws esz sgn loader sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
  `array_len_ok F cnt loader base_op (drop_fresh sa s) (n2w cnt)` by
    simp[array_len_ok_static] >>
  drule_all compile_array_subscript_oob >> strip_tac >>
  `straight_fresh (compile_array_subscript base_op idx_op F cnt ws esz sgn loader)` by
    simp[straight_fresh_compile_array_subscript] >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem array_check_ptr_run:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (op,sb) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  eval_operand len_op s = SOME len /\ fresh_vars_wrt sa s /\
  idx_in_range sgn i len ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz)
Proof
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  drule_all array_bounds_check_ok >> strip_tac >>
  forward_all_evals >> drule_all array_elem_ptr_run >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem array_check_ptr_oob:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (op,sb) /\
  eval_operand idx_op s = SOME i /\ eval_operand len_op s = SOME len /\
  fresh_vars_wrt sa s /\ ~idx_in_range sgn i len ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  drule_all array_bounds_check_oob >> strip_tac >>
  `straight_fresh (array_bounds_check idx_op len_op sgn)` by
    (rw[array_bounds_check_def, array_bounds_valid_def] >>
     rpt (FIRST [irule straight_fresh_bind >> conj_tac,
                 gen_tac >> BETA_TAC,
                 irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
                 irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
                 MATCH_ACCEPT_TAC straight_fresh_return,
                 IF_CASES_TAC])) >>
  `straight_fresh (array_elem_ptr base_op idx_op dyn ws esz)` by
    (rw[array_elem_ptr_def] >>
     rpt (FIRST [irule straight_fresh_bind >> conj_tac,
                 gen_tac >> BETA_TAC,
                 irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
                 MATCH_ACCEPT_TAC straight_fresh_return,
                 IF_CASES_TAC])) >>
  gvs[straight_fresh_def] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`sa`, `cs'`, `sb`, `s`] mp_tac
    arithmeticPropsTheory.abort_propagates >> simp[]
QED

Theorem runtime_array_subscript_counted_oob:
  compile_array_subscript base_op idx_op T cnt ws esz sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_imm_load_word F imm base_op sa = (lop,sm)` >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     drule emit_op_extends >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> simp[] >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]) >>
  `cs_extends sm sb` by metis_tac[straight_fresh_cs_extends] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_imm_load_word_runtime_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_operand lop t = SOME len` >>
  `eval_operand idx_op t = SOME i /\
   (!z. idx_op = Var z ==> not_fresh_at sm z) /\
   (!z. lop = Var z ==> not_fresh_at sm z)` by
    (drule_all compile_imm_load_word_runtime_run >> strip_tac >>
     qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
     conj_tac
     >- (Cases_on `idx_op` >> gvs[eval_operand_def] >>
         drule lookup_var_update_not_fresh >> simp[]) >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `!z. idx_op = Var z ==> _` drule >>
     simp[not_fresh_at_def] >> disch_then irule >> decide_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `eval_operand idx_op (drop_fresh sm u) = SOME i /\
   eval_operand lop (drop_fresh sm u) = SOME len /\
   fresh_vars_wrt sm (drop_fresh sm u)` by
    (simp[varsExtTheory.fresh_vars_wrt_drop_fresh,
          eval_operand_drop_fresh, Abbr `u`]) >>
  drule_all array_check_ptr_oob >> strip_tac >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `u`] >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func s 0 (OK u)` by simp[Abbr `u`] >>
  drule_all gas_marked_path_then >> simp[] >> metis_tac[]
QED

Theorem runtime_array_subscript_counted_ok:
  compile_array_subscript base_op idx_op T cnt ws esz sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand op t = SOME ((b + n2w ws) + i * n2w esz) /\
    (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==> lookup_var z t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_imm_load_word F imm base_op sa = (lop,sm)` >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     drule emit_op_extends >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> simp[] >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]) >>
  `cs_extends sm sb` by metis_tac[straight_fresh_cs_extends] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_imm_load_word_runtime_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_operand lop t = SOME len` >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i /\
   (!z. base_op = Var z ==> not_fresh_at sm z) /\
   (!z. idx_op = Var z ==> not_fresh_at sm z) /\
   (!z. lop = Var z ==> not_fresh_at sm z) /\
   (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
   stmt_state_rel ctx func cenv cx es (t with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (drule_all compile_imm_load_word_runtime_run >> strip_tac >> gvs[] >>
     drule_all compile_imm_load_word_runtime_frame >>
     disch_then (qspec_then `len` strip_assume_tac) >>
     qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime] >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
     conj_tac
     >- (Cases_on `base_op` >> gvs[eval_operand_def] >>
         drule lookup_var_update_not_fresh >> simp[]) >>
     conj_tac
     >- (Cases_on `idx_op` >> gvs[eval_operand_def] >>
         drule lookup_var_update_not_fresh >> simp[]) >>
     simp[not_fresh_at_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt conj_tac >> rpt strip_tac
     >- (qpat_x_assum `!z. base_op = Var z ==> _` drule >>
         simp[not_fresh_at_def] >> disch_then irule >> decide_tac)
     >- (qpat_x_assum `!z. idx_op = Var z ==> _` drule >>
         simp[not_fresh_at_def] >> disch_then irule >> decide_tac) >>
     qpat_x_assum `!n. _ <= n ==> _` (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `eval_operand base_op (drop_fresh sm u) = SOME b /\
   eval_operand idx_op (drop_fresh sm u) = SOME i /\
   eval_operand lop (drop_fresh sm u) = SOME len /\
   fresh_vars_wrt sm (drop_fresh sm u)` by
    simp[varsExtTheory.fresh_vars_wrt_drop_fresh,
         eval_operand_drop_fresh, Abbr `u`] >>
  drule_all array_check_ptr_run >> strip_tac >>
  `~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `u`] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es u` by simp[Abbr `u`] >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK (t'' with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexists_tac `t'' with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[Abbr `u`] >> rpt strip_tac >>
  qpat_x_assum `!z v. not_fresh_at sm z /\ _ ==> _`
    (qspecl_then [`z`, `v`] irule) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!z. not_fresh_at sa z ==> _` drule >>
      simp[lookup_var_def]) >>
  irule not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]
QED

(* Successful source selection after an index which preserves the captured
   non-storage base's source memory and immutable maps. *)
Theorem framed_array_select_read:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  t'.scopes = t.scopes /\ t'.immutables = t.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  (vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode \/
   (?n. bd = Fixed n)) /\
  read_result cx r t' = (INL (ArrayV av),t') /\
  array_index (ArrayTV etv bd) av i = SOME v ==>
  ?child. select_result cx (ArrayT et bd) r (ValueSubscript (IntV i)) t' =
            (INL child,t') /\
          read_result cx child t' = (INL v,t')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av)
      [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_array_subscript_result] >>
  Cases_on `r`
  >~ [`read_result cx (HashMapRef tr slot tv key) _ = _`] >-
    gvs[read_result_def, raise_def]
  >~ [`Value value`] >-
    (gvs[read_result_def, return_def] >>
     drule_all select_value_read >> metis_tac[]) >>
  drule_all expr_body_pre_place_metadata >> strip_tac >>
  gnvs[] >>
  drule_all expr_body_pre_popped_keys_indexed >> strip_tac >>
  Cases_on `p`
  >~ [`StoragePlace tr slot vt`] >- metis_tac[]
  >~ [`MemoryPlace id path`] >-
    (qpat_x_assum `_ \/ _` strip_assume_tac
     >- (drule_all expr_body_pre_code_not_memory >> simp[]) >>
     gvs[] >>
     `runtime_place_typed cx t' (MemoryPlace id path) (ArrayTV etv (Fixed n))`
       by gvs[vyperPlaceTypingTheory.runtime_place_typed_memory] >>
     `popped_keys_indexed t'.scopes` by simp[] >>
     drule_all select_fixed_memory_read >> metis_tac[]) >>
  rename1 `ImmutablePlace src id path` >>
  `runtime_place_typed cx t' (ImmutablePlace src id path) (ArrayTV etv bd)` by
    (qpat_x_assum `runtime_place_typed _ _ _ _` mp_tac >>
     Cases_on `ALOOKUP t.immutables cx.txn.target` >>
     simp[vyperPlaceTypingTheory.runtime_place_typed_immutable,
          get_immutables_def, get_address_immutables_def, bind_def,
          return_def, raise_def]) >>
  drule_all select_typed_immutable_read >> metis_tac[]
QED

Theorem vv_post_array_element:
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sb s0 es' r
    (LocatedValue ann p) s /\
  expr_type obj = ArrayT et bd /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  (p.ptr_location = LocMemory ==> ?n. bd = Fixed n) /\
  eval_operand p.ptr_operand s = SOME w /\
  read_result cx r es' = (INL (ArrayV av),es') /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf etv v /\ value_has_type etv v /\
  read_result cx child es' = (INL v,es') /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst s = SOME (w + n2w j) /\
  (!id path'. child = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV i)] /\ r = PlaceR (MemoryPlace id path)) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sb s0 es' child
    (LocatedValue et (mk_ptr dst p.ptr_location)) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_holds cenv cx (ArrayT et bd) r (LocatedValue ann p) es' s` by
    gvs[vv_post_def, vyperASTTheory.expr_type_def] >>
  drule_all vv_holds_array_element >> strip_tac >>
  `vv_at cenv cx et sa sb es' child (LocatedValue et (mk_ptr dst p.ptr_location)) s` by
    (Cases_on `p.ptr_location = LocMemory`
     >- (fs[] >> gnvs[] >> rename1 `expr_type obj = ArrayT et (Fixed n)` >>
         `vv_at cenv cx (ArrayT et (Fixed n)) sa sb es' r (LocatedValue ann p) s`
           by gvs[vv_post_def, vyperASTTheory.expr_type_def] >>
         `mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
            SOME (Num i * type_memory_size etv,etv)` by
           (Cases_on `av` >>
            gvs[mem_step_offset_def, vyperValueOperationTheory.array_index_def,
                valueEncodingDefsTheory.val_wf_def, listTheory.oEL_THM,
                AllCaseEqs()]) >>
         drule_all vv_at_fixed_array_element >> simp[]) >>
     `vv_at cenv cx (ArrayT et bd) sa sb es' r (LocatedValue ann p) s`
       by gvs[vv_post_def, vyperASTTheory.expr_type_def] >>
     pop_assum mp_tac >>
     simp[vv_at_def, contextTheory.mk_ptr_def, compileEnvTheory.is_word_type_def] >>
     metis_tac[]) >>
  gvs[vv_post_def, vyperASTTheory.expr_type_def, expr_has_effect_thm, contextTheory.mk_ptr_def] >>
  first_assum ACCEPT_TAC
QED
