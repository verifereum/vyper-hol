(*
 * Pop on a nested target: the target fragment judgment (pop_target_frag),
 * the shared helpers and the storage case with pure indices
 * (pop_nested_storage_pure_sim).  Split from exprSimPopNested so that
 * its residual cases, each in its own theory, can use them.
 *)

Theory exprSimPopNestedBase
Ancestors
  exprSimHashBoundary
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHypsDefs exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases targetPlaceLive vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv loweringStateRelDefs finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation
  exprSimHash fragGasSeqAbort gasSummary exprSimVVFrame stmtSimProps
  gasOutcome gasExemptCert gasSummaryCompose fragGasMode fragGasPath


(* The target's fragment, typed ty, evaluates to a place at the pointer
   (target_place_sim's conclusion, at every start). *)
Definition pop_target_frag_def:
  pop_target_frag ctx func cenv cx env bt es <=>
    !ty sa sb r s0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome F (cx_tops cx) (ctx, func) (eval_target_place cx bt)
        (es, s0)
        (\res ee t. ?p. res = INL p /\
          target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type ty)
            r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts)
        (\res ee r. expr_exit res r)
End

Theorem pop_target_frag_of_sim:
  !ctx func cenv cx env bt es.
    target_sim ctx func cenv cx env bt es ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  rw[pop_target_frag_def] >> irule target_place_sim >> metis_tac[]
QED

Definition nested_pop_suffix_def:
  nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 =
    [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr; Var x3] [];
     mk_inst (id+6) ADD [hdr; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]]
End

Theorem nested_pop_suffix_shape:
  !hdr tr esz is_ctor imm sa r sb.
    compile_dynarray_pop hdr 1 esz is_ctor imm
      (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        nested_pop_suffix hdr tr sa.cs_next_id esz x0 x1 x2 x3 x4 x5 x6
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_dynarray_pop_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def,
       emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[APPEND_ASSOC] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var + 1))`,
                `STRING #"%" (toString (sa.cs_next_var + 2))`,
                `STRING #"%" (toString (sa.cs_next_var + 3))`,
                `STRING #"%" (toString (sa.cs_next_var + 4))`,
                `STRING #"%" (toString (sa.cs_next_var + 5))`] >>
  simp[ASCIInumbersTheory.toString_11, not_fresh_at_def, APPEND_ASSOC,
       nested_pop_suffix_def]
QED

Theorem nested_pop_step_load:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) s =
    OK (update_var out (if tr then tload (THE (eval_operand hdr s)) s
                       else sload (THE (eval_operand hdr s)) s) s)
Proof
  Cases_on `tr` >> Cases_on `eval_operand hdr s` >>
  simp[step_inst_base_def, exec_read1_def, mk_inst_def]
QED

Theorem nested_pop_step_store:
  IS_SOME (eval_operand hdr s) /\ IS_SOME (lookup_var x s) /\
  ~s.vs_call_ctx.cc_static ==>
  step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [hdr; Var x] []) s =
    OK (if tr then tstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s
        else sstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s)
Proof
  Cases_on `tr` >> Cases_on `eval_operand hdr s` >> Cases_on `lookup_var x s` >>
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, exec_write2_def, mk_inst_def,
       eval_operand_def]
QED

Theorem nested_pop_step_add:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id ADD [hdr; Lit 1w] [out]) s =
    OK (update_var out (THE (eval_operand hdr s) + 1w) s)
Proof
  Cases_on `eval_operand hdr s` >> simp[] >>
  irule step_ADD >> simp[eval_operand_def]
QED


Theorem nested_pop_suffix_empty:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a s'. run_inst_seq
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = Abort a s'
Proof
  Cases_on `hdr` >>
  simp[eval_operand_def] >> strip_tac >>
  fs[nested_pop_suffix_def, run_inst_seq_def, nested_pop_step_load,
     pop_step_ISZERO, pop_step_ASSERT, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]
QED

Theorem nested_pop_suffix_run:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?u. run_inst_seq
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    u = (if tr then tstore slot (tload slot s - 1w) s
         else sstore slot (sload slot s - 1w) s) with vs_vars := u.vs_vars /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==> lookup_var x u = lookup_var x s) /\
    lookup_var x6 u = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz)
Proof
  Cases_on `hdr` >> simp[eval_operand_def] >> strip_tac >>
  fs[nested_pop_suffix_def, run_inst_seq_def, nested_pop_step_load,
     nested_pop_step_store, nested_pop_step_add,
     pop_step_ISZERO, pop_step_ASSERT, pop_step_SUB_lit,
     pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
  Cases_on `tr` >>
  fs[nested_pop_step_store, nested_pop_step_add,
     pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, sstore_def, tstore_def] >>
  simp[venom_state_component_equality, FLOOKUP_UPDATE] >> rw[] >> gvs[]
QED

(* A storage or transient root whose indices are pure (no pop, no call).
   compile_get_target_ptr hands out the array's header slot with location
   storage (transient), and the source's pop_place pops the StoragePlace
   there, so the run is compile_pop_storage_sim's at that slot: the header
   load, the abort on zero, the store of the length less one, and the last
   element's slot.  The element is past the new length, so its slots are
   dead in the array; storage_holds asks for them to agree
   (storage_range_agree), before the pop by storage_rel and after it since
   only the header slot changed.  Pure indices leave the state alone, so
   the header the target points at stays live. *)
Theorem nested_pop_storage_dead_header:
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\ storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) j b
Proof
  strip_tac >> fs[storage_dead_def] >>
  rename1 `dead_bytes st (w2n k) tv' j b` >>
  qexistsl [`mid'`, `n'`, `subs'`, `k`, `tv'`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  Cases_on `(k,tv') = (root_slot,root)`
  >- (gvs[] >> irule nested_pop_dead_bytes_subregion >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl [`tv`, `n`, `path`] >> simp[]) >>
  `ranges_disjoint (w2n k) (type_slot_size tv')
                   (w2n root_slot) (type_slot_size root)` by
    (first_x_assum irule >> metis_tac[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `dead_bytes (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
     (w2n k) tv' j b = dead_bytes st (w2n k) tv' j b` suffices_by simp[] >>
  irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
  match_mp_tac nested_pop_lookup_frame >>
  gvs[vyperStorageFrameTheory.ranges_disjoint_def,
      vyperValueTheory.type_slot_size_def] >> decide_tac
QED

Theorem nested_pop_stmt_state_rel_header:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr
      (update_storage slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1))
        (get_storage cx es tr)))
    (if tr then
       tstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s
     else
       sstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s)
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx _ _ _ es1 s1` >>
  `accounts_rel cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`]
     >- (irule accountsRelPropsTheory.accounts_rel_tstore >> simp[] >> qexists `es` >>
         simp[vyperStorageBackendTheory.set_storage_backend_eq, vyperStorageBackendTheory.get_storage_def, vfmStateTheory.lookup_account_def] >>
         rpt strip_tac >> irule nested_pop_storage_dead_header >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     irule accountsRelPropsTheory.accounts_rel_sstore >> simp[] >> qexists `es` >>
     simp[vyperStorageBackendTheory.set_storage_backend_eq, vyperStorageBackendTheory.get_storage_def, vfmStateTheory.lookup_account_def] >>
     rpt strip_tac >> irule nested_pop_storage_dead_header >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]) >>
  drule accountsRelPropsTheory.accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`] >>
     fs[stmt_state_rel_def, state_rel_def, sstore_def, tstore_def, LET_THM,
        vyperStorageBackendTheory.set_storage_def, local_ptrs_rel_def, local_backed_def, local_region_def,
        lookup_var_def, immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, sstore_def, tstore_def, LET_THM,
          vyperStorageBackendTheory.set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]
QED

Theorem nested_pop_live_array_agree:
  stmt_state_rel ctx func cenv cx es s /\
  storage_read_live cx tr (vyperStorageBackend$get_storage cx es tr) slot (ArrayTV tv (Dynamic n)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) ==>
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic n))
Proof
  strip_tac >> irule accountsRelPropsTheory.storage_range_agree_of_live >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cx`, `tr`] >> simp[] >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
      transient_rel_def, vyperStorageBackendTheory.get_storage_def,
      vfmStateTheory.lookup_account_def]
QED

Theorem nested_pop_array_header_load:
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic n)) ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (vyperStorageBackend$get_storage cx es tr)
Proof
  strip_tac >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all accountsRelPropsTheory.storage_range_agree_head >>
  Cases_on `tr` >> simp[sload_def, tload_def]
QED

Theorem nested_pop_updated_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\
  local_ptrs_reserved cenv sa /\
  u = (if tr then tstore slot
         (n2w (w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr)) - 1)) s
       else sstore slot
         (n2w (w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr)) - 1)) s)
        with vs_vars := u.vs_vars /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes slot [(0,n2w (w2n (lookup_storage slot
        (vyperStorageBackend$get_storage cx es tr)) - 1))]
        (vyperStorageBackend$get_storage cx es tr))) u
Proof
  strip_tac >> drule_all nested_pop_stmt_state_rel_header >> strip_tac >>
  qpat_x_assum `w2n slot = _` kall_tac >>
  Cases_on `tr` >> gvs[] >>
  simp[vyperStorageTheory.apply_writes_def] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  first_x_assum (drule_then mp_tac) >>
  gvs[sstore_def, tstore_def, lookup_var_def, LET_THM]
QED

Theorem nested_pop_positive_holds:
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) w (ArrayTV tv (Dynamic n)) /\
  slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n w) (ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage w (vyperStorageBackend$get_storage cx es tr)) /\ 0 < len /\
  elem = w + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore w (n2w (len - 1)) s else sstore w (n2w (len - 1)) s)
        with vs_vars := u.vs_vars ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes w [(0,n2w (len - 1))] (vyperStorageBackend$get_storage cx es tr))) u
Proof
  strip_tac >>
  `len <= n` by metis_tac[pop_array_length_bound] >>
  `w2n w + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by
    fs[accountsRelPropsTheory.storage_range_agree_def] >>
  Q.SUBGOAL_THEN
    `w2n elem + type_slot_size tv <= dimword(:256) /\
     (type_slot_size tv = 0 \/ w2n w < w2n elem)` assume_tac
  >- metis_tac[pop_array_last_bounds] >>
  `slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n elem) tv` by
    metis_tac[pop_array_last_slots] >>
  `storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) elem tv` by
    metis_tac[storage_range_agree_dyn_last] >>
  irule pop_storage_holds >>
  pure_rewrite_tac[vyperStorageBackendTheory.get_storage_after_set] >>
  conj_tac >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[pop_element_slots_frame] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  `storage_range_agree
     (apply_writes w [(0,n2w (len - 1))] (vyperStorageBackend$get_storage cx es tr))
     (apply_writes w [(0,n2w (len - 1))]
       (if tr then contract_transient s else contract_storage s)) elem tv` by
    metis_tac[storage_pop_element_frame] >>
  Cases_on `tr` >>
  gvs[contract_storage_def, contract_transient_def, sstore_def, tstore_def,
      LET_THM, vyperStorageTheory.apply_writes_def, vfmStateTheory.lookup_account_def]
QED

Theorem nested_pop_target_callback_cong:
  !bt f g cenv.
    (!e. MEM e (target_indices bt) ==> !ce t st. f ce t e st = g ce t e st) ==>
    compile_get_target_ptr f cenv bt = compile_get_target_ptr g cenv bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_def] >> rpt strip_tac
  >~ [`compile_get_target_ptr _ _ (NameTarget _)`]
  >- simp[compile_get_target_ptr_def]
  >~ [`compile_get_target_ptr _ _ (TopLevelNameTarget _)`]
  >- simp[compile_get_target_ptr_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  `compile_get_target_ptr f cenv b = compile_get_target_ptr g cenv b` by
    (first_x_assum irule >> metis_tac[]) >>
  pure_rewrite_tac[compile_get_target_ptr_def] >>
  asm_rewrite_tac[] >>
  `f cenv (expr_type e) e = g cenv (expr_type e) e` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  `lower_value f cenv (expr_type e) e = lower_value g cenv (expr_type e) e` by
    simp[lower_value_def, comp_bind_def, FUN_EQ_THM] >>
  asm_rewrite_tac[]
QED

Theorem nested_pop_index_size:
  !bt e. MEM e (target_indices bt) ==> expr_size e < base_assignment_target_size bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_def, expr_size_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  strip_tac >> res_tac >> decide_tac
QED

Theorem nested_pop_target_guard_erasure:
  compile_get_target_ptr
    (expr_child_callback (expr_size (Pop ann bt)) f) cenv bt =
  compile_get_target_ptr f cenv bt
Proof
  irule nested_pop_target_callback_cong >> rpt strip_tac >>
  irule exprCallBoundsTheory.expr_child_callback_valid >>
  drule nested_pop_index_size >> simp[expr_size_def]
QED

Theorem nested_pop_compile_eq:
  compile_expr cenv ty (Pop ann bt) sa =
    (let ((hdr,loc_opt,pt_opt),sm) = compile_get_target_ptr compile_expr cenv bt sa in
     let loc = (case loc_opt of SOME l => l | NONE => LocMemory) in
     let et = (case pt_opt of SOME (ValPT (ArrayT t _)) => t | _ => BaseT (IntT 256)) in
     let (elem,sb) = compile_dynarray_pop hdr (word_scale loc)
       (elem_size_in_location cenv loc et)
       cenv.ce_is_ctor cenv.ce_imm_alloca loc sm in
     (LocatedValue ann (mk_ptr elem loc),sb))
Proof
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def, SRULE [expr_size_def] nested_pop_target_guard_erasure,
       SF ETA_ss] >>
  `compile_get_target_ptr
     (expr_child_callback (base_assignment_target_size bt + (type_size ann + 1)) compile_expr)
       cenv bt = compile_get_target_ptr compile_expr cenv bt` by
    (irule nested_pop_target_callback_cong >> rpt strip_tac >>
     irule exprCallBoundsTheory.expr_child_callback_valid >>
     drule nested_pop_index_size >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem nested_pop_compile_storage_eq:
  compile_get_target_ptr compile_expr cenv bt sa =
    ((hdr,SOME (if tr then LocTransient else LocStorage),
      SOME (ValPT (ArrayT et (Dynamic n)))),sm) ==>
  compile_expr cenv ty (Pop ann bt) sa =
    (let (elem,sb) = compile_dynarray_pop hdr 1
       (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
       cenv.ce_is_ctor cenv.ce_imm_alloca
       (if tr then LocTransient else LocStorage) sm in
     (LocatedValue ann (mk_ptr elem (if tr then LocTransient else LocStorage)),sb))
Proof
  strip_tac >> rewrite_tac[nested_pop_compile_eq] >>
  Cases_on `tr` >> simp[word_scale_def]
QED

Theorem nested_pop_extend_storage_class:
  ((?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt vt. pv = HashMapRef tr slot kt vt)) /\
  extend_place cx pv sb st = (INL next,st') ==>
  (?tr slot tv. next = PlaceR (StoragePlace tr slot tv)) \/
  (?tr slot kt vt. next = HashMapRef tr slot kt vt)
Proof
  strip_tac
  >- (gvs[extend_place_def, bind_def, return_def, AllCaseEqs()] >>
      drule extend_storage_place_subregion >> strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `sb` >>
  gvs[extend_place_def, bind_def, return_def, raise_def, lift_option_type_def,
      AllCaseEqs()] >>
  Cases_on `vt` >>
  gvs[extend_place_def, bind_def, return_def, raise_def, lift_option_type_def,
      AllCaseEqs()] >> metis_tac[]
QED

Theorem nested_pop_lookup_storage_class:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
  lookup_global cx src id st = (INL pv,st') ==>
  (?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
  (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  PairCases_on `d` >> Cases_on `d0` >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[return_def, bind_def, lift_option_type_def, raise_def, AllCaseEqs()] >>
  gvs[return_def] >> metis_tac[]
QED

Theorem nested_pop_eval_base_storage_class:
  !bt cx st pv st' src id ts d.
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    eval_base_place cx bt st = (INL pv,st') ==>
    (?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
    (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_root_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule_all nested_pop_lookup_storage_class >> simp[]) >>
  simp[target_root_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_base_place cx child st = (INL child_pv,child_st)` >>
  qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule nested_pop_extend_storage_class >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem nested_pop_eval_target_storage_class:
  target_root bt = TopLevelNameTarget (src,id) /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
  eval_target_place cx bt st = (INL p,st') ==>
  ?tr slot tv. p = StoragePlace tr slot tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_storage_class >> strip_tac >>
  gvs[get_place_def, return_def, raise_def] >> metis_tac[]
QED

Theorem nested_pop_storage_target_metadata:
  target_post ctx func cenv cx es sa sm s0 es' (PlaceR (StoragePlace tr slot vt))
    (Type (ArrayT ann (Dynamic n))) (hdr,loc,pt) t ==>
  ?tv. vt = ArrayTV tv (Dynamic n) /\
    evaluate_type (get_tenv cx) ann = SOME tv /\
    eval_operand hdr t = SOME slot /\ loc = SOME (slot_loc tr) /\
    pt = SOME (ValPT (ArrayT ann (Dynamic n))) /\
    (!x. hdr = Var x ==> not_fresh_at sm x) /\
    stmt_state_rel ctx func cenv cx es' t
Proof
  simp[target_post_def, place_ptr_rel_def, value_type_place_def,
       vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem nested_pop_storage_natural_region:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) ==>
  ?mid name keys root root_tv path delta.
    declared_storage_region cx mid name keys = SOME (tr,root,root_tv) /\
    storage_subregion root_tv path delta (ArrayTV tv (Dynamic n)) /\
    slot = root + n2w delta /\ w2n slot = w2n root + delta /\
    w2n root + type_slot_size root_tv <= dimword(:256) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)
Proof
  strip_tac >> fs[storage_place_region_def] >>
  drule_all vyperStorageLayoutSafetyTheory.storage_layout_safe_region_nonoverflow >> strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root + delta < dimword(:256)` by
    (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `delta < dimword(:256)` by decide_tac >>
  `w2n (n2w delta : bytes32) = delta` by simp[] >>
  `w2n (root + n2w delta : bytes32) = w2n root + delta` by
    simp[wordsTheory.w2n_add_2] >>
  qexistsl [`mid`, `var_name`, `keys`, `root`, `tv'`, `path`, `delta`] >>
  simp[] >> decide_tac
QED

Theorem nested_pop_slots_word_offset:
  slots_in_range raw (w2n (w:bytes32) + off) tv ==>
  slots_in_range raw (w2n (w + n2w off)) tv
Proof
  strip_tac >>
  `slots_in_range raw (w2n w + off) tv =
   slots_in_range raw (w2n (w + n2w off)) tv` by
    (irule (cj 1 vyperLookupStorageTheory.slots_in_range_offset_cong) >>
     `w + n2w off = n2w (w2n w + off)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     simp[wordsTheory.w2n_n2w]) >> gvs[]
QED

Theorem nested_pop_tuple_slots_index:
  !tvs k off raw.
    tuple_slots_in_range raw off tvs /\ k < LENGTH tvs ==>
    slots_in_range raw (off + tuple_prefix_slot_size k tvs) (EL k tvs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `tuple_slots_in_range _ _ _` mp_tac >>
  simp[Once vyperLookupStorageTheory.slots_in_range_def] >> strip_tac >>
  Cases_on `k` >> gvs[tuple_prefix_slot_size_def] >>
  first_x_assum drule_all >> rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem nested_pop_tuple_slots:
  slots_in_range raw (w2n (w:bytes32)) (TupleTV tvs) /\
  oEL k tvs = SOME tv ==>
  slots_in_range raw (w2n (w + n2w (tuple_prefix_slot_size k tvs))) tv
Proof
  strip_tac >> irule nested_pop_slots_word_offset >>
  gvs[listTheory.oEL_EQ_EL] >> irule nested_pop_tuple_slots_index >>
  simp[GSYM vyperLookupStorageTheory.slots_in_range_def]
QED

Theorem nested_pop_fixed_slots:
  slots_in_range raw (w2n (w:bytes32)) (ArrayTV tv (Fixed n)) /\ k < n ==>
  slots_in_range raw (w2n (w + n2w (k * type_slot_size tv))) tv
Proof
  strip_tac >> irule nested_pop_slots_word_offset >>
  gvs[Once vyperLookupStorageTheory.slots_in_range_def,
      vyperLookupStorageTheory.array_slots_in_range_indexed]
QED

Theorem nested_pop_dynamic_slots:
  slots_in_range raw (w2n (w:bytes32)) (ArrayTV tv (Dynamic n)) /\
  k < w2n (lookup_storage w raw) ==>
  slots_in_range raw (w2n (w + n2w (k * type_slot_size tv + 1))) tv
Proof
  strip_tac >> irule nested_pop_slots_word_offset >>
  qpat_x_assum `slots_in_range _ _ _` mp_tac >>
  simp[Once vyperLookupStorageTheory.slots_in_range_def,
       vyperLookupStorageTheory.array_slots_in_range_indexed,
       vyperStorageTheory.read_slot_def] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >>
  simp[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem nested_pop_extend_storage_slots:
  get_storage_backend cx tr st = (INL raw,st) /\
  slots_in_range raw (w2n slot) tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' slot' tv'),st') ==>
  tr' = tr /\ slots_in_range raw (w2n slot') tv'
Proof
  reverse (Cases_on `sb`)
  >- (Cases_on `tv` >>
      simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[return_def] >>
      irule vyperLookupStorageTheory.storage_field_slots_in_range >> metis_tac[]) >>
  Cases_on `v` >> Cases_on `tv` >> simp[extend_storage_place_def, raise_def]
  >~ [`slots_in_range _ _ (TupleTV _)`]
  >- (simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      irule nested_pop_tuple_slots >> metis_tac[]) >>
  rename1 `ArrayTV elem bd` >> Cases_on `bd` >>
  simp[resolve_array_element_def, bind_def, ignore_bind_def,
       lift_option_type_def, check_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[vyperStoragePlaceProvenanceTheory.resolve_array_element_empty, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, return_def, raise_def, AllCaseEqs()]
  >- (irule nested_pop_fixed_slots >> metis_tac[]) >>
  irule nested_pop_dynamic_slots >> metis_tac[]
QED

Definition nested_pop_result_slots_def:
  nested_pop_result_slots cx st (PlaceR (StoragePlace tr slot tv)) =
    (!raw. get_storage_backend cx tr st = (INL raw,st) ==>
       slots_in_range raw (w2n slot) tv) /\
  nested_pop_result_slots cx st (PlaceR _) = T /\
  nested_pop_result_slots cx st (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  nested_pop_result_slots cx st (Value _) = T
End

Theorem nested_pop_mapping_leaf_slots:
  contract_storage_well_formed cx st /\
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  slots_in_range raw (w2n slot) tv
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `slot`, `tv`] mp_tac) >>
  asm_simp_tac bool_ss [vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def,
                       optionTheory.option_case_def, APPEND_NIL] >>
  strip_tac >>
  drule_all vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >> simp[]
QED

Theorem nested_pop_lookup_global_slots:
  contract_storage_well_formed cx st /\
  lookup_global cx mid var_name st = (INL pv,st') ==>
  nested_pop_result_slots cx st pv
Proof
  Cases_on `pv` >> simp[nested_pop_result_slots_def]
  >- (Cases_on `p` >> simp[nested_pop_result_slots_def] >> rpt strip_tac >>
      drule lookup_global_storage_region >> strip_tac >>
      drule_all vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >> simp[]) >>
  strip_tac >> drule lookup_global_mapping_region >> simp[]
QED

Theorem nested_pop_extend_result_slots:
  contract_storage_well_formed cx st /\
  nested_pop_result_slots cx st pv /\
  extend_place cx pv sb st = (INL pv',st') ==>
  nested_pop_result_slots cx st pv'
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def, nested_pop_result_slots_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >~ [`extend_storage_place _ _ _ _ _ _`]
      >- (drule extend_storage_place_subregion >> strip_tac >> gvs[] >>
          simp[nested_pop_result_slots_def] >> rpt strip_tac >>
          gvs[nested_pop_result_slots_def] >>
          drule_all nested_pop_extend_storage_slots >> simp[]) >>
      simp[extend_memory_place_def, nested_pop_result_slots_def]) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  Cases_on `v` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[nested_pop_result_slots_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v'` assume_tac) >>
  simp[] >> rpt strip_tac >>
  irule nested_pop_mapping_leaf_slots >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem nested_pop_eval_base_slots:
  !bt cx st pv st'.
    contract_storage_well_formed cx st /\
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') ==>
    nested_pop_result_slots cx st pv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >> rpt strip_tac >> gvs[] >>
      simp[nested_pop_result_slots_def] >>
      metis_tac[nested_pop_lookup_global_slots]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  simp[nested_pop_result_slots_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[]
  >~ [`pure_expr e`]
  >- (drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule_all nested_pop_extend_result_slots >> simp[]) >>
  drule_all nested_pop_extend_result_slots >> simp[]
QED

Theorem nested_pop_eval_target_slots:
  contract_storage_well_formed cx st /\
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  slots_in_range raw (w2n slot) tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_slots >> strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def,
                       nested_pop_result_slots_def]
QED

Theorem nested_pop_suffix_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  code = nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    (Cases_on `tr` >> simp[nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  drule_all hash_run_path >>
  Cases_on `tr` >> simp[nested_pop_suffix_def, mk_inst_def]
QED

Theorem nested_pop_suffix_abort_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code /\
  code = nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq code s = Abort a t ==>
  ?j. gas_marked_path F ctx func s 0 (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >> irule run_inst_seq_abort_zero_path >>
  fs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `code` >>
  Cases_on `tr` >>
  gvs[nested_pop_suffix_def, mk_inst_def, is_terminator_def, DROP_APPEND]
QED

Theorem nested_pop_storage_gas_obs:
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,ee) ==>
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
    (es with gas_obs := gs) = (res,ee with gas_obs := gs)
Proof
  Cases_on `tr` >>
  simp[pop_place_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, ignore_bind_def, check_def, assert_def, return_def, raise_def,
       vyperStorageBackendTheory.write_storage_slot_eq,
       vyperStorageBackendTheory.get_storage_def,
       vyperStorageBackendTheory.set_storage_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem nested_pop_target_admissible:
  gas_admissible (eval_expr cx (Pop ann bt)) expr_vv_res_ok es ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  simp[gasContextTheory.gas_admissible_def, target_place_res_ok_def] >>
  rpt strip_tac >> Cases_on `res` >> simp[] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[Once evaluate_def, bind_def, expr_vv_res_ok_def] >>
  metis_tac[]
QED

Theorem nested_pop_suffix_vv_post:
  target_post ctx func cenv cx es sa sm s0 mid pv vt op t /\
  ci_mono sa sm /\ stmt_state_rel ctx func cenv cx es' u /\
  storage_holds cx tr ann v slot es' u /\ lookup_var x u = SOME slot /\
  u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
  (!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t) ==>
  vv_post ctx func cenv cx (Pop ann bt) es sa r s0 es' v
    (LocatedValue ann (mk_ptr (Var x) (if tr then LocTransient else LocStorage))) u
Proof
  strip_tac >>
  `!q. not_fresh_at sa q ==> not_fresh_at sm q` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  Cases_on `tr` >>
  (fs[target_post_def, vv_post_def, vv_holds_def, vv_at_def,
      contextTheory.mk_ptr_def, eval_operand_def, expr_type_def,
      locals_kept_def, expr_has_effect_thm] >> rpt strip_tac >> gvs[]
   >- (qpat_assum `!aid off sz. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
       simp[] >> metis_tac[]) >>
   metis_tac[])
QED

(* The pop suffix on a storage dynarray whose place is a storage region,
   in range (slots_in_range) and live (storage_read_live) in the
   storage at the target's end.  Pure indices give these facts
   (nested_pop_storage_suffix_sim); so do indices that leave storage
   alone (exprSimPopNestedStorageFrame). *)
Theorem nested_pop_storage_live_suffix_sim:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) /\
  slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n slot)
    (ArrayTV tv (Dynamic n)) /\
  storage_read_live cx tr (vyperStorageBackend$get_storage cx es tr) slot
    (ArrayTV tv (Dynamic n)) /\
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
    (Type (ArrayT ann (Dynamic n))) (hdr,SOME (slot_loc tr),pt) t /\
  compile_dynarray_pop hdr 1 (type_slot_size tv) cenv.ce_is_ctor
    cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sm = (q,r) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,es') /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\ es.gas_obs = [] /\
  fn_has_code sm r func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))) (es,t)
    (\res fin u. ?v. res = INL v /\ vv_post ctx func cenv cx (Pop ann bt) es0 sa r s0 fin v
      (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) u /\
      u.vs_current_bb = r.cs_current_bb /\ u.vs_inst_idx = LENGTH r.cs_current_insts)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `!tail. pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
       (es with gas_obs := tail) = (res,es' with gas_obs := tail)` by
    metis_tac[nested_pop_storage_gas_obs] >>
  `stmt_state_rel ctx func cenv cx es t` by fs[target_post_def] >>
  `~cx.txn.is_static /\ ~t.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule_all nested_pop_storage_natural_region >> strip_tac >>
  drule_all nested_pop_live_array_agree >> strip_tac >>
  drule nested_pop_array_header_load >> strip_tac >>
  qpat_x_assum `storage_layout_safe _` kall_tac >>
  qpat_x_assum `storage_place_region _ _` kall_tac >>
  qpat_x_assum `storage_read_live _ _ _ _ _` kall_tac >>
  qpat_x_assum `pop_place _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss())
      [pop_place_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, ignore_bind_def, check_def, assert_def, return_def, raise_def,
       vyperStorageBackendTheory.write_storage_slot_eq,
       vyperStorageTheory.encode_value_def, vyperStorageTheory.encode_base_to_slot_def,
       integer_wordTheory.i2w_def]) >>
  Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr) = 0w`
  >- (simp[assert_def, bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
      drule nested_pop_suffix_shape >> strip_tac >> suspend "empty") >>
  `0 < w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr))` by
    (Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr)` >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule nested_pop_suffix_shape >> strip_tac >> suspend "positive"
QED

Resume nested_pop_storage_live_suffix_sim[empty]:
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (fs[] >> metis_tac[]) >>
  drule_all nested_pop_suffix_empty >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  `?j. gas_marked_path F ctx func t 0 (Abort a (s' with vs_inst_idx := j))` by
    (irule nested_pop_suffix_abort_path >> simp[] >> metis_tac[]) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty storage array"))`, `es`,
    `Abort a (s' with vs_inst_idx := j)`] >>
  simp[expr_exit_def, exit_result_def] >>
  qpat_x_assum `!tail. pop_place _ _ _ = _`
    (mp_tac o REWRITE_RULE [pop_place_def, check_def, ignore_bind_def]) >>
  simp[]
QED

Resume nested_pop_storage_live_suffix_sim[positive]:
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
   (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6])` by
    (fs[] >> metis_tac[]) >>
  ` (if tr then tload (root + n2w delta) t else sload (root + n2w delta) t) <> 0w` by
    metis_tac[] >>
  drule_all nested_pop_suffix_run >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  qpat_x_assum `ALL_DISTINCT [x6; x5; x4; x3; x2; x1; x0]` kall_tac >>
  qpat_x_assum `ALL_DISTINCT [x0; x1; x2; x3; x4; x5; x6]` kall_tac >>
  qmatch_asmsub_abbrev_tac `eval_operand hdr t = SOME slot` >>
  qmatch_asmsub_abbrev_tac `0 < w2n lenw` >>
  `lenw - 1w = n2w (w2n lenw - 1)` by
    (simp[wordsTheory.n2w_sub]) >>
  `u = (if tr then tstore slot (n2w (w2n lenw - 1)) t
         else sstore slot (n2w (w2n lenw - 1)) t) with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q t` by
    (fs[ci_mono_def, not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> fs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `stmt_state_rel ctx func cenv cx
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes slot [(0,n2w (w2n lenw - 1))]
        (vyperStorageBackend$get_storage cx es tr))) u` by
    (`w2n slot = w2n root + delta` by simp[arithmeticTheory.ADD_COMM] >>
     qunabbrev_tac `lenw` >> drule_all nested_pop_updated_state_rel >> simp[]) >>
  qmatch_asmsub_abbrev_tac
    `stmt_state_rel ctx func cenv cx fin u` >>
  `storage_holds cx tr ann
    (PlaceR (StoragePlace tr (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) tv))
    (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) fin u` by
    (qunabbrev_tac `fin` >> qunabbrev_tac `lenw` >>
     irule nested_pop_positive_holds >>
     rpt conj_tac >- first_assum ACCEPT_TAC >- REFL_TAC >- REFL_TAC
     >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`n`, `t`] >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qpat_assum `w2n slot = _` (fn th => REWRITE_TAC [th]) >>
         first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `u = _ with vs_vars := _` (fn th => ONCE_REWRITE_TAC [th]) >>
     Cases_on `tr` >>
     simp_tac (srw_ss()) [NoAsms, sstore_def, tstore_def, LET_THM]) >>
  qpat_x_assum `u = _ with vs_vars := _` kall_tac >>
  qpat_x_assum `u = _ with vs_vars := _` kall_tac >>
  `lookup_var x6 u =
     SOME (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv))` by
    (qpat_x_assum `lookup_var x6 u = _` mp_tac >>
     qpat_x_assum `(if tr then tload _ _ else sload _ _) = _`
       (fn th => REWRITE_TAC [th]) >>
     qpat_x_assum `lenw - 1w = _` (fn th => REWRITE_TAC [th]) >>
     simp_tac (srw_ss()) [NoAsms, wordsTheory.word_mul_n2w,
       GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC]) >>
  `!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t` by
    (rpt strip_tac >> qpat_assum `!x. ~MEM x _ ==> _` irule >>
     fs[] >> rpt strip_tac >> gvs[]) >>
  `fin with gas_obs := [] = fin` by
    (qunabbrev_tac `fin` >> Cases_on `tr` >>
     simp[vyperStorageBackendTheory.set_storage_def,
          evaluation_state_component_equality]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `sb` |-> `r`, `s` |-> `t`, `t` |-> `u`,
                  `id` |-> `sm.cs_next_id`, `esz` |-> `type_slot_size tv`,
                  `code` |-> `nested_pop_suffix hdr tr sm.cs_next_id
                     (type_slot_size tv) x0 x1 x2 x3 x4 x5 x6`]
          nested_pop_suffix_path) >>
  impl_tac >- simp[] >> strip_tac >>
  `res = INL (PlaceR (StoragePlace tr
            (slot + n2w (1 + (w2n lenw - 1) * type_slot_size tv)) tv)) /\
   es' = fin` by
    (qpat_x_assum `_ es = (res,es')` mp_tac >>
     simp[Abbr `fin`, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def,
          vyperStorageBackendTheory.write_storage_slot_eq,
          vyperStorageTheory.encode_value_def,
          vyperStorageTheory.encode_base_to_slot_def,
          integer_wordTheory.i2w_def] >>
     strip_tac >> gvs[] >>
     simp[arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM]) >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`res`, `es'`,
    `OK (u with vs_inst_idx := LENGTH r.cs_current_insts)`] >>
  simp[exprSimVVFrameTheory.vv_post_inst_idx] >>
  irule nested_pop_suffix_vv_post >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_x_assum `storage_holds _ _ _ _ _ fin u` mp_tac >> simp[]
QED

Finalise nested_pop_storage_live_suffix_sim

Theorem nested_pop_storage_suffix_sim:
  expr_sim_inv cenv cx env es /\
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt es = (INL (StoragePlace tr slot (ArrayTV tv (Dynamic n))),es) /\
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
    (Type (ArrayT ann (Dynamic n))) (hdr,SOME (slot_loc tr),pt) t /\
  compile_dynarray_pop hdr 1 (type_slot_size tv) cenv.ce_is_ctor
    cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sm = (q,r) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,es') /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm /\ es.gas_obs = [] /\
  fn_has_code sm r func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))) (es,t)
    (\res fin u. ?v. res = INL v /\ vv_post ctx func cenv cx (Pop ann bt) es0 sa r s0 fin v
      (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) u /\
      u.vs_current_bb = r.cs_current_bb /\ u.vs_inst_idx = LENGTH r.cs_current_insts)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx es` by
    fs[expr_sim_inv_def] >>
  `storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))` by
    metis_tac[eval_target_place_region] >>
  `get_storage_backend cx tr es = (INL (vyperStorageBackend$get_storage cx es tr),es)` by
    simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
  drule_all nested_pop_eval_target_slots >> strip_tac >>
  drule_all nested_pop_eval_target_live >> strip_tac >>
  drule_all nested_pop_storage_live_suffix_sim >> simp[]
QED



(* Counted form (why it still holds after the GAS join):
   - eval_expr cx (Pop _ bt) = bind (eval_target_place cx bt) (pop_place cx).
   - pop_target_frag (counted, via gas_outcome) gives the target's outcome:
     a gas summary or an exemption certificate.  Exemptions and target
     exceptions lift through the bind unchanged.
   - Pure indices: eval_target_place leaves the whole state alone at every
     state, gas_obs included (targetPlaceLive.nested_pop_eval_target_pure_state),
     so the target end state is es up to gas_obs.
   - pop_place on a StoragePlace reads no gas (write_storage_slot_gas_obs
     in stmtSimAssignStorage is the analogous fact for the write).
   - The pop suffix (nested_pop_suffix_def) has no GAS, INVOKE or
     terminator, so its straight-line run is a 0-count path
     (exprSimHash.hash_run_path, fragGasSeqAbort.run_inst_seq_abort_zero_path).
     The SSTORE/TSTORE in it needs ~cc_static, which stmt_state_rel at the
     target's end state supplies (state_rel), as does ~cx.txn.is_static for
     the source write.
   - The facts the old frag_exec proof used are all still here; only the
     composition changes. *)
Theorem pop_nested_storage_pure_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt)` by
    fs[expr_body_pre_def] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[well_typed_expr_def] >>
  pop_assum strip_assume_tac >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  PairCases_on `q` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr _ _ _ _ = ((hdr,loc,pt),sm)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  Cases_on
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `!h w e c i l s. ci_mono s (SND (compile_dynarray_pop h w e c i l s))` by
    simp[ci_mono_compile_dynarray_pop] >>
  `ci_mono sm r` by metis_tac[pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm r func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    metis_tac[nested_pop_target_admissible] >>
  qpat_x_assum `pop_target_frag _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [pop_target_frag_def]) >>
  disch_then (qspecl_then [`ArrayT ann (Dynamic n)`, `sa`, `sm`,
                           `(hdr,loc,pt)`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  `eval_expr cx (Pop ann bt) = vyperState$bind (eval_target_place cx bt) (pop_place cx)` by
    simp[FUN_EQ_THM, Once evaluate_def, vyperStateTheory.bind_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> suspend "summary") >>
  disj2_tac >> rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  first_assum (irule_at Any o MATCH_MP gas_exempt_cert_error_place)
QED

Resume pop_nested_storage_pure_sim[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`tres`, `tend`, `tr0`] strip_assume_tac) >>
  gvs[]
  >- suspend "normal" >>
  Cases_on `tres` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR exc) tr0` >>
  qexistsl_tac [`INR exc`, `tend`, `tr0`] >> simp[] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  metis_tac[expr_exit_INR_type]
QED

Resume pop_nested_storage_pure_sim[normal]:
  rename1 `target_post _ _ _ _ _ _ _ _ _ (PlaceR p) _ _ t` >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p, tend with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all nested_pop_eval_target_pure_state >> strip_tac >>
  `gas_explicit marks s0.vs_gas_readings = [] /\
   tend with gas_obs := [] = es with gas_obs := []` by
    fs[evaluation_state_component_equality] >>
  qpat_x_assum `_ with gas_obs := [] = _ with gas_obs := gas_explicit _ _`
    kall_tac >>
  gvs[] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  drule_all nested_pop_eval_target_storage_class >> strip_tac >> gvs[] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule_all pop_storage_element_size >>
  disch_then (qspec_then `tr` assume_tac) >>
  fs[GSYM slot_loc_def] >>
  `ws = 1` by
    (Cases_on `tr` >> fs[Abbr `ws`, Abbr `lc`, slot_loc_def, word_scale_def]) >>
  qunabbrev_tac `lc` >> qunabbrev_tac `ws` >>
  gvs[Abbr `esz`] >>
  simp[slot_loc_def] >>
  rename1 `evaluate_type (get_tenv cx) ann = SOME tv` >>
  Cases_on `pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))
              (es with gas_obs := [])` >>
  rename1 `_ = (pres, pend)` >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := []`, `es0` |-> `es`,
                  `res` |-> `pres`, `es'` |-> `pend`,
                  `pt` |-> `SOME (ValPT (ArrayT ann (Dynamic n)))`]
          nested_pop_storage_suffix_sim) >>
  impl_tac >- fs[slot_loc_def] >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choosel_then [`pres'`, `pend'`, `pr`]
                (CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`pres'`, `pend'`, `pr`] >>
  conj_tac
  >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
             |> REWRITE_RULE [APPEND_NIL]) >>
      qpat_assum `gas_marked_exec _ _ (eval_target_place _ _) _ _ _ _ _`
        (irule_at Any) >>
      asm_rewrite_tac[]) >>
  gvs[]
QED

Finalise pop_nested_storage_pure_sim


