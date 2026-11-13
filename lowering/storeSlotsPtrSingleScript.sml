(* A sparse singleton accepts any stable clean storage address operand. *)
Theory storeSlotsPtrSingle
Ancestors storeSlotsPtrInterface assignBasePtrStorageSingle
  assignBasePtrStoragePath emitHelperProps fragExec stateFrame
  ptrDiscipline bodyPtrDefs fragGasPathPtr venomState finite_map
  list rich_list words arithmetic emitHelper compileEnv loweringStateRelDefs
  venomInst context stmtSimStoreCopy

Theorem store_slots_single_shape:
  (do loaded <- emit_op MLOAD [Var root];
      emit_void (if tr then TSTORE else SSTORE) [slot;loaded]
   od) sa = (z,sb) /\ fn_has_code sa sb func ==>
  ?tmp bb.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [Var root] [tmp];
       mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [slot;Var tmp] []] /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    (!j. j < LENGTH sb.cs_current_insts ==>
      get_instruction bb j = SOME (EL j sb.cs_current_insts)) /\
    (!x. not_fresh_at sa x ==> x <> tmp)
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> gvs[fn_has_code_def] >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  simp[not_fresh_at_def] >> gvs[IS_PREFIX_APPEND, get_instruction_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[EL_APPEND_EQN] >>
  rpt strip_tac >> Cases_on `j < LENGTH sa.cs_current_insts` >- simp[] >>
  `j = LENGTH sa.cs_current_insts \/ j = LENGTH sa.cs_current_insts + 1` by decide_tac >>
  gvs[]
QED

Theorem store_slots_single_compiled_counted:
  (do loaded <- emit_op MLOAD [Var root];
      emit_void (if tr then TSTORE else SSTORE) [slot;loaded]
   od) sa = (z,sb) /\ fn_has_code sa sb func /\
  not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
  op_taint tn slot = {} /\ ptr_covers G tn root s 32 /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tf (OK u) /\
    store_slots_ptr_frame tr sw dw s tn [0] u tf /\
    ptr_covers Gf tf root u 32 /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_labels = s.vs_labels /\
    u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all store_slots_single_shape >> strip_tac >>
  `root <> tmp /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id MLOAD [Var root] [tmp]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [slot;Var tmp] [])` by
    (simp[EL_APPEND_EQN] >> metis_tac[ADD1]) >>
  drule_all assign_base_storage_load_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 g1 t1 (OK s1)` >>
  `eval_operand slot s1 = SOME dw /\ op_taint t1 slot = {}` by
    (Cases_on `slot` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [slot;Var tmp] []) /\
   eval_operand (Var tmp) s1 = SOME (mload (w2n sw) s) /\
   ~s1.vs_call_ctx.cc_static` by simp[eval_operand_def, EL_APPEND_EQN, ADD1] >>
  drule_all assign_base_storage_write_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] assume_tac) >>
  qexistsl_tac [`g1`,
    `if tr then t1 with t_trans := key_update t1.t_trans dw (op_taint t1 (Var tmp))
     else t1 with t_stor := key_update t1.t_stor dw (op_taint t1 (Var tmp))`,
    `(if tr then tstore dw (mload (w2n sw) s) s1 else sstore dw (mload (w2n sw) s) s1)
      with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  Cases_on `tr` >>
  gvs[store_slots_ptr_frame_def, store_slots_taint_def, FOLDL,
    store_copy_normalize_def, execution_frame_def, sstore_def, tstore_def,
    ptr_covers_def, lookup_var_def, op_taint_def, ADD1, WORD_ADD_0,
    venom_state_component_equality] >> metis_tac[]
QED
