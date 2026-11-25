(* Fixed selection from a reached local memory place. *)
Theory bodyArrayMemoryFixedSuffixMods
Ancestors
  bodyArrayNoCopyCutsMods bodyArrayFramedMemoryAddressMods
  bodyFullSubscriptArrayCodeBounds bodyFullPathHistory
  bodyForRangeScalarFrameMods gasOutcomeFullPostMods
  exprSimSubscriptArraySource exprSimSubscriptArraySuffix
  exprSimSubscriptArrayFramed exprSimVVFrame exprSimBopRestWordLoads
  exprSimProps exprSimWordArgs exprSimHash exprSimMemDefs exprOperandVar
  bodyFullUnwrapRun bodyPtrDefs exprLoweringProps emitHelperProps
  stmtSimForArray valueTypingMemoryProps valueEncodingProps valueEncoding
  loweringPosts loweringStateRelDefs exprLowering compileEnv ptrDiscipline
  context fragGasOriginPtr fragExec gasExplicitSites venomState venomInst
  vyperArray vyperState vyperAST vyperInterpreter vyperValueOperation
  vyperTypeSystem vyperTypeValues vyperTyping vyperStorageFootprint
  overflowElimHelpers words integer_word finite_map pair
  exprSimArrayIndex loweringShapeRules exprSimDefs arithmetic
  bodyFullPostsMods vyperAssignPreservesType exprSimCopy
  stateRelProj bodyFullHashKeccakFixed freshWrites
Libs
  monadsyntax

Theorem fixed_code_parts[local]:
  compile_array_subscript bop iop F n ws sz signed loader sn = (dst,sb) /\
  fn_has_code sn sb fn ==>
  ?sc sm offset out.
    array_bounds_check iop (Lit (n2w n)) signed sn = ((),sc) /\
    fn_has_code sn sc fn /\
    emit_op MUL [iop;Lit (n2w sz)] sc = (Var offset,sm) /\
    emit_op ADD [bop;Var offset] sm = (Var out,sb) /\
    dst = Var out /\ sn.cs_next_id <= sb.cs_next_id
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[oneTheory.one] >>
  rename1 `array_bounds_check _ _ _ sn = ((),sc)` >>
  `ci_mono sn sc` by
    (qpat_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
     Cases_on `signed` >> simp[NoAsms,array_bounds_check_def,array_bounds_valid_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_emit_void, irule ci_mono_comp_return])) >>
  `ci_mono sc sb` by
    (qpat_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [SND] o Q.AP_TERM `SND`) >>
     simp[NoAsms,array_elem_ptr_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op, irule ci_mono_comp_return])) >>
  `fn_has_code sn sc fn` by metis_tac[fn_has_code_split,ci_mono_def] >>
  `sn.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[array_elem_ptr_def,comp_bind_def,comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[] >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  gvs[]
QED

Theorem fixed_valid_index[local]:
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV tv (Fixed n)) /\
  i = (if signed then w2i iw else &(w2n iw)) ==>
  (idx_in_range signed iw (n2w n) <=> valid_index (ArrayTV tv (Fixed n)) (SArrayV kvs) i) /\
  (idx_in_range signed iw (n2w n) ==> 0 <= i /\ Num i < n /\ w2n iw = Num i)
Proof
  strip_tac >> drule_then strip_assume_tac evaluated_fixed_array_bound >>
  `idx_in_range signed iw (n2w n) <=> 0 <= i /\ i < &n` by
    (drule idx_in_range_integer >> disch_then (qspecl_then [`iw`,`signed`] mp_tac) >> simp[]) >>
  conj_tac >- simp[valid_index_def,array_length_def] >>
  `0 <= i /\ i < &n ==> Num i < n` by (rpt (pop_assum kall_tac) >> intLib.COOPER_TAC) >>
  disch_tac >> `0 <= i /\ i < &n` by fs[] >>
  Cases_on `signed` >> gvs[] >>
  drule overflowElimHelpersTheory.nonneg_w2i_eq_w2n >> simp[]
QED

Theorem fixed_place_reject[local]:
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV tv (Fixed n)) /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (SArrayV kvs)),fin) /\
  ~valid_index (ArrayTV tv (Fixed n)) (SArrayV kvs) i ==>
  !gs. select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
         (ValueSubscript (IntV i)) (fin with gas_obs := gs) =
       (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := gs)
Proof
  strip_tac >>
  `evaluate_subscripts (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs))
      [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index")` by
    (irule evaluate_array_subscript_oob >> simp[]) >>
  `select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
       (ValueSubscript (IntV i)) fin =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)` by
    (irule select_nonstorage_place_error >> simp[] >>
     qexists `ArrayTV tv (Fixed n)` >> simp[]) >>
  gen_tac >>
  `SND (select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
       (ValueSubscript (IntV i)) fin) = fin` by simp[] >>
  drule_then mp_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`r` |-> `PlaceR (MemoryPlace id path)`] select_result_nonstorage_gas_obs)) >> simp[]
QED

Theorem fixed_child_bytes[local]:
  evaluate_type (get_tenv cx) et = SOME tv /\ value_has_type tv v /\
  read_result cx child fin = (INL v,fin) /\
  eval_operand (Var out) q = SOME w /\ op_taint tq (Var out) = {} /\
  (!m. mem_agree_outside tq.t_mem q.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
  (type_memory_size tv <> 0 ==> w2n w + type_memory_size tv <= q.vs_alloca_next) /\
  (type_memory_size tv <> 0 ==> ?b sz. FLOOKUP Gq out = SOME (b,sz) /\
     b <= w2n w /\ w2n w + type_memory_size tv <= b + sz) /\
  type_memory_bytes ce et = type_memory_size tv ==>
  vv_holds_mods ce cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) fin q /\
  vv_store_bound cx et et fin child (LocatedValue et (mk_ptr (Var out) LocMemory)) q /\
  ptr_vv_ok cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) fin Gq tq q /\
  ptr_buf_ok ce (Subscript et obj idx) (Var out) Gq q
Proof
  strip_tac >>
  `val_wf tv v` by simp[value_has_type_memory_wf] >>
  `val_store_size tv v <= type_memory_size tv /\ val_footprint tv v <= type_memory_size tv` by
    simp[val_store_size_le,val_footprint_le] >>
  `val_in_memory tv v (w2n w) q.vs_memory` by simp[mem_agree_outside_def] >>
  conj_tac
  >- (simp[vv_holds_mods_def,vv_holds_def,mk_ptr_def] >> strip_tac >>
      drule_all val_in_memory_word_type >> simp[]) >>
  conj_tac >- (simp[vv_store_bound_def,mk_ptr_def] >> decide_tac) >>
  conj_tac
  >- (simp[ptr_vv_ok_def,mk_ptr_def,ptr_mem_ok_def] >> strip_tac >>
      `type_memory_size tv <> 0` by decide_tac >>
      qpat_assum `type_memory_size tv <> 0 ==> ?b sz. _` (drule_then strip_assume_tac) >>
      qexistsl [`b`,`sz`] >> simp[] >> decide_tac) >>
  simp[ptr_buf_ok_def,lowered_value_type_def,expr_type_def] >> disch_tac >>
  qpat_assum `type_memory_size tv <> 0 ==> ?b sz. _` (drule_then strip_assume_tac) >>
  qexistsl [`b`,`sz`] >> asm_rewrite_tac[] >> decide_tac
QED

Theorem fixed_child_pointer[local]:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) sz) /\ lookup_var root q = SOME bw /\
  ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME rtval /\
  mem_path_offset rtval path = SOME (k,ArrayTV tv (Fixed n)) /\
  mem_step_offset (ArrayTV tv (Fixed n)) (ValueSubscript (IntV i)) = SOME (j,tv) /\
  eval_operand (Var out) q = SOME (a + n2w j) /\ a = bw + n2w k ==>
  vv_place_ptr_mods ce cx fin q (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr (Var out) LocMemory))
Proof
  strip_tac >> drule_all_then assume_tac mem_path_offset_snoc >>
  simp[vv_place_ptr_mods_def,vv_place_ptr_def,mk_ptr_def,GSYM word_add_n2w,
       AC WORD_ADD_ASSOC WORD_ADD_COMM]
QED

Theorem array_memory_fixed_suffix_mods:
  compile_array_subscript bop iop F n ws (type_memory_size tv)
    (is_signed_type (expr_type idx)) loader sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV tv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME tv /\
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV tv (Fixed n)) /\
  popped_keys_indexed fin.scopes /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (SArrayV kvs)),fin) /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  vv_at ce cx (ArrayT et (Fixed n)) sa sn fin (PlaceR (MemoryPlace id path))
    (LocatedValue ann (mk_ptr bop LocMemory)) u /\
  (?root sz bw rt rtval k.
     FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) sz) /\ lookup_var root u = SOME bw /\
     ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME rtval /\
     mem_path_offset rtval path = SOME (k,ArrayTV tv (Fixed n)) /\ a = bw + n2w k) /\
  w2n a + n * type_memory_size tv < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) (w2n a) m) /\
  (type_memory_size tv <> 0 ==> w2n a + n * type_memory_size tv <= u.vs_alloca_next) /\
  (type_memory_size tv <> 0 ==> ?b sz. op_prov G bop = SOME (b,sz) /\
      b <= w2n a /\ w2n a + n * type_memory_size tv <= b + sz) /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\ (!l. bop <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\ (!l. iop <> Label l) /\
  allocas_from lo u /\ alloca_history fn u /\ fn_inst_ids_distinct fn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  type_memory_bytes ce et = type_memory_size tv /\
  sa.cs_next_var <= sn.cs_next_var /\ local_ptrs_reserved ce sn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  wb_frame ce es fin sa s0 u /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 u) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx fin u /\ immutable_frame_mods fn ce cx fin u /\
    storage_well_formed_on cx fin (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx fin G tn u) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,fn) ce cx et obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sb,dst,LocMemory) (PlaceR (MemoryPlace id path),IntV i) (fin,u,G,tn)
Proof
  strip_tac >>
  drule_all_then (qspec_then `kvs` strip_assume_tac) fixed_valid_index >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  drule_all_then strip_assume_tac fixed_code_parts >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)`
  >- suspend "accept" >>
  suspend "reject"
QED

Resume array_memory_fixed_suffix_mods[reject]:
  `~valid_index (ArrayTV tv (Fixed n)) (SArrayV kvs) i` by fs[] >>
  drule_all_then (qspec_then `et` assume_tac) fixed_place_reject >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n) /\
   op_taint tn (Lit (n2w n)) = {} /\ op_prov G (Lit (n2w n)) = NONE /\
   (!x. iop = Var x \/ Lit (n2w n) = Var x ==> not_fresh_at sn x) /\
   (!l. iop <> Label l /\ Lit (n2w n) <> Label l)` by
    simp[eval_operand_def,op_taint_def,op_prov_def] >>
  drule_all array_bounds_check_joint_oob_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gq`,`tq`,`q`] strip_assume_tac)) >>
  simp[array_select_outcome_mods_def] >> irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl [`Gq`,`fin`,`Abort Revert_abort q`,
            `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tq`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def]
QED

Resume array_memory_fixed_suffix_mods[accept]:
  `valid_index (ArrayTV tv (Fixed n)) (SArrayV kvs) i /\
   0 <= i /\ Num i < n /\ w2n iw = Num i` by fs[] >>
  drule array_index_valid >> simp[optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `v` assume_tac) >>
  `evaluate_subscripts (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs))
     [ValueSubscript (IntV i)] = INL v` by simp[evaluate_array_subscript_result] >>
  drule_all_then (qspec_then `ArrayT et (Fixed n)` strip_assume_tac) select_fixed_memory_read >>
  qabbrev_tac `child = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))` >>
  `!gs. select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
     (ValueSubscript (IntV i)) (fin with gas_obs := gs) = (INL child,fin with gas_obs := gs)` by
    (simp[Abbr `child`] >> gen_tac >>
     `SND (select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
       (ValueSubscript (IntV i)) fin) = fin` by simp[] >>
     drule_then mp_tac (SIMP_RULE (srw_ss()) []
        (Q.INST [`r` |-> `PlaceR (MemoryPlace id path)`] select_result_nonstorage_gas_obs)) >> simp[]) >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  drule_all (framed_memory_fixed_address_run
    |> INST_TYPE [Type.alpha |-> ``:256``]
    |> Q.INST [`i` |-> `w2n (iw:bytes32)`] |> SRULE []) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gq`,`tq`,`q`] strip_assume_tac)) >>
  pop_assum (mk_asm "state_tail") >>
  qabbrev_tac `j = Num i * type_memory_size tv` >>
  `j = Num i * type_memory_size tv` by simp[Abbr `j`] >>
  `lookup_var out q = SOME (a + n2w j)` by
    (qpat_assum `lookup_var out q = _` mp_tac >> asm_rewrite_tac[]) >>
  `val_wf (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs))` by
    simp[value_has_type_memory_wf] >>
  `w2n (a + n2w j) = w2n a + j` by
    (qpat_assum `j = _` SUBST1_TAC >> irule fixed_array_element_nonwrapping >>
     goal_assum (drule_at (Pat `array_index _ _ _ = _`)) >>
     simp[NoAsms,val_footprint_def,type_memory_size_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `j + type_memory_size tv <= n * type_memory_size tv` by
    (`(Num i + 1) * type_memory_size tv <= n * type_memory_size tv` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     qpat_x_assum `(Num i + 1) * _ <= _` mp_tac >>
     rewrite_tac[RIGHT_ADD_DISTRIB,MULT_LEFT_1] >> decide_tac) >>
  suspend "element"
QED

Resume array_memory_fixed_suffix_mods[element]:
  qpat_assum `evaluate_type _ et = SOME tv`
    (mp_then Any assume_tac evaluate_type_well_formed_type_value) >>
  `value_has_type tv v` by
    (irule array_index_has_type >> simp[] >> qexistsl [`SArrayV kvs`,`Fixed n`,`i`] >> simp[]) >>
  `val_wf tv v` by simp[value_has_type_memory_wf] >>
  `eval_operand (Var out) q = SOME (a + n2w j)` by
    (pure_rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `eval_operand bop q = SOME a` by
    (qpat_assum `eval_operand bop u = SOME a` mp_tac >>
     qpat_assum `!l. bop <> Label l` mp_tac >>
     qpat_assum `!x. bop = Var x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `bop` >> simp[eval_operand_def]) >>
  `mem_step_offset (ArrayTV tv (Fixed n)) (ValueSubscript (IntV i)) = SOME (j,tv)` by
    asm_rewrite_tac[mem_step_offset_def] >>
  `not_fresh_at sn root` by (drule_all environment_var_not_fresh >> simp[]) >>
  `lookup_var root q = SOME bw` by simp[] >>
  `vv_place_ptr_mods ce cx fin q child (LocatedValue et (mk_ptr (Var out) LocMemory))` by
    (simp[Abbr `child`] >> irule fixed_child_pointer >>
     goal_assum (drule_at (Pat `mem_path_offset _ _ = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
     qexistsl [`a`,`bw`,`j`,`rt`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!nm b len. local_region ce fin.scopes q nm b len <=> local_region ce fin.scopes u nm b len` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `sn` >> simp[]) >>
  `vv_at ce cx (ArrayT et (Fixed n)) sa sb fin (PlaceR (MemoryPlace id path))
     (LocatedValue ann (mk_ptr bop LocMemory)) q` by
    (irule vv_at_vars_frame >> qexistsl [`u`,`sn`] >> simp[vv_operand_def,mk_ptr_def]) >>
  `vv_at ce cx et sa sb fin child (LocatedValue et (mk_ptr (Var out) LocMemory)) q` by
    (irule vv_at_fixed_array_element >>
     qpat_assum `vv_at _ _ _ _ sb fin _ _ q` (irule_at Any) >>
     goal_assum (drule_at (Pat `mem_step_offset _ _ = _`)) >>
     qexistsl [`a`,`v`,`a + n2w j`,`SArrayV kvs`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (simp[NoAsms,mk_ptr_def] >> first_assum ACCEPT_TAC) ORELSE
       (simp[NoAsms,Abbr `child`] >> rpt gen_tac >>
        rpt (pop_assum kall_tac) >> metis_tac[]))) >>
  suspend "bytes"
QED

Resume array_memory_fixed_suffix_mods[bytes]:
  `!m. mem_agree_outside tq.t_mem q.vs_memory m ==> val_in_memory tv v (w2n (a + n2w j)) m` by
    (qpat_assum `tq.t_mem = _` SUBST1_TAC >> qpat_assum `q.vs_memory = _` SUBST1_TAC >>
     qpat_assum `w2n (a + n2w j) = _` SUBST1_TAC >>
     qpat_assum `j = _` SUBST1_TAC >>
     `&(Num i) = i` by intLib.COOPER_TAC >>
     `array_index (ArrayTV tv (Fixed n)) (SArrayV kvs) (&(Num i)) = SOME v` by simp[] >>
     rpt strip_tac >>
     `val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV kvs)) (w2n a) m` by simp[] >>
     qpat_x_assum `array_index _ _ (&Num i) = _`
       (mp_then Any mp_tac rest_word_array_memory_index) >>
     disch_then (qspecl_then [`w2n a`,`m`] mp_tac) >> simp[NoAsms] >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `type_memory_size tv <> 0 ==> w2n (a + n2w j) + type_memory_size tv <= q.vs_alloca_next` by
    (strip_tac >> `w2n a + n * type_memory_size tv <= u.vs_alloca_next` by simp[] >> decide_tac) >>
  `type_memory_size tv <> 0 ==> ?b sz. FLOOKUP Gq out = SOME (b,sz) /\
      b <= w2n (a + n2w j) /\ w2n (a + n2w j) + type_memory_size tv <= b + sz` by
    (disch_tac >> qpat_assum `type_memory_size tv <> 0 ==> ?b sz. _`
        (drule_then strip_assume_tac) >>
     qexistsl [`b`,`sz'`] >> conj_tac
     >- (qpat_assum `op_prov Gq (Var out) = op_prov G bop` mp_tac >>
         qpat_assum `op_prov G bop = SOME _` SUBST1_TAC >> simp[NoAsms,op_prov_def]) >>
     qpat_assum `w2n (a + n2w j) = _` SUBST1_TAC >> decide_tac) >>
  `vv_holds_mods ce cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) fin q /\
   vv_store_bound cx et et fin child (LocatedValue et (mk_ptr (Var out) LocMemory)) q /\
   ptr_vv_ok cx et child (LocatedValue et (mk_ptr (Var out) LocMemory)) fin Gq tq q /\
   ptr_buf_ok ce (Subscript et obj idx) (Var out) Gq q` by
    (irule fixed_child_bytes >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`tv`,`v`,`a + n2w j`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "outcome"
QED

Resume array_memory_fixed_suffix_mods[outcome]:
  rewrite_tac[array_select_outcome_mods_def,LET_THM] >> BETA_TAC >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gq`,`fin`,`INL child`,`q`,`tq`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `fin with gas_obs := [] = fin` by
    (simp[NoAsms,evaluation_state_component_equality] >> first_assum ACCEPT_TAC) >>
  qpat_assum `fin with gas_obs := [] = fin` SUBST1_TAC >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _` (drule_then strip_assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,fn,PG)
     (u,G,tn) [] (OK q,Gq,tq)` by (first_assum irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `stmt_state_rel H ctx fn ce cx fin q` by (asm "state_tail" irule >> asm_rewrite_tac[]) >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel H _ _ _ _ _ u`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[NoAsms]) >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  qpat_assum `stmt_state_rel H _ _ _ _ _ q`
    (mp_then Any assume_tac stmt_state_rel_allocas_below_fmp) >>
  suspend "frames"
QED

Resume array_memory_fixed_suffix_mods[frames]:
  `immutable_frame_mods fn ce cx fin q` by
    (irule immutable_frame_mods_exterior_frame >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
     qexists `sn` >> asm_rewrite_tac[] >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at sn x ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `wb_frame ce es fin sa s0 q` by
    (irule wb_frame_readonly_tail >> qexistsl [`sn`,`u`] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> _` (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `~expr_has_effect (Subscript et obj idx) ==> pure_frame ce fn es sa s0 q` by
    (disch_tac >> irule pure_frame_mem_tail >> qexists `u` >> asm_rewrite_tac[] >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at_mods (DF H) lo d ce cx fin Gq tq q` by
    (irule ghost_inv_at_mods_exterior_frame >>
     goal_assum (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
     qexists `sn` >> asm_rewrite_tac[]) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gq tq` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >>
     asm_rewrite_tac[] >> reverse conj_tac >- simp[NoAsms] >>
     qx_gen_tac `x` >> disch_tac >>
     `not_fresh_at sn x` by (irule not_fresh_at_mono >> qexists `sa` >> asm_rewrite_tac[]) >>
     qpat_assum `!x. not_fresh_at sn x ==> _` (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `vv_post_mods H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin child
     (LocatedValue et (mk_ptr (Var out) LocMemory)) q` by
    (qpat_assum `wb_frame _ _ _ _ _ q` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     simp[NoAsms,vv_post_mods_def,expr_type_def] >>
     rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (qpat_assum `~expr_has_effect (Subscript _ _ _) ==> pure_frame _ _ _ _ _ _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) ORELSE
      simp[NoAsms,vv_storage_live_def,mk_ptr_def])) >>
  BETA_TAC >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by asm_rewrite_tac[] >>
  simp[NoAsms,expr_type_def,lowered_value_type_def] >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (simp[NoAsms,Abbr `child`,vv_location_def,mk_ptr_def] >>
    qpat_assum `ptr_buf_ok _ _ (Var out) Gq q` (ACCEPT_TAC o REWRITE_RULE [])))
QED

Finalise array_memory_fixed_suffix_mods
