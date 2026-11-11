(* The direct singleton branch is exactly one memory load and one store. *)
Theory assignBasePtrStorageSingle
Ancestors stmtSimStoreCopy assignBasePtrStorageLayout assignBasePtrStoragePath
  assignBasePtrStorageLoop stateFrame context compileEnv loweringStateRelDefs emitHelper
  emitHelperProps fragExec bodyPtrDefs venomState ptrDiscipline
  fragGasPathPtr finite_map pred_set list rich_list arithmetic words venomInst

Theorem assign_base_storage_single_shape:
  !tr root k sa z sb fn.
    (do loaded <- emit_op MLOAD [Var root];
        emit_void (if tr then TSTORE else SSTORE) [Lit k;loaded]
     od) sa = (z,sb) /\ fn_has_code sa sb fn ==>
    ?tmp bb.
      sb.cs_current_bb = sa.cs_current_bb /\
      sb.cs_current_insts = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id MLOAD [Var root] [tmp];
         mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [Lit k;Var tmp] []] /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
      (!j. j < LENGTH sb.cs_current_insts ==>
        get_instruction bb j = SOME (EL j sb.cs_current_insts)) /\
      (!x. not_fresh_at sa x ==> x <> tmp)
Proof
  rpt gen_tac >>
  simp[emit_op_def, emit_void_def, emit_inst_def, comp_ignore_bind_def,
    comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  gvs[fn_has_code_def] >>
  qexists_tac `STRING #"%" (toString sa.cs_next_var)` >>
  simp[not_fresh_at_def] >>
  gvs[IS_PREFIX_APPEND, get_instruction_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[EL_APPEND_EQN] >> rpt strip_tac >>
  Cases_on `j < LENGTH sa.cs_current_insts` >- simp[] >>
  `j = LENGTH sa.cs_current_insts \/ j = LENGTH sa.cs_current_insts + 1` by decide_tac >>
  gvs[]
QED

Theorem assign_base_storage_single_counted:
  !s fn bb id tr root tmp a k tn G ctx D PG.
    ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var root] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) (if tr then TSTORE else SSTORE) [Lit k;Var tmp] []) /\
    ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\ root <> tmp /\
    ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s 1) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn 1 u tf /\
      ptr_covers Gf tf root u 32 /\ lookup_var root u = SOME a /\
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx+2 /\ ~u.vs_halted /\
      (!x. x <> tmp ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_base_storage_load_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `g1` (qx_choose_then `t1` (qx_choose_then `s1` strip_assume_tac))) >>
  `~s1.vs_halted /\ lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx =
     SOME (mk_inst (id+1) (if tr then TSTORE else SSTORE) [Lit k;Var tmp] []) /\
   eval_operand (Lit k) s1 = SOME k /\
   eval_operand (Var tmp) s1 = SOME (mload (w2n a) s) /\
   op_taint t1 (Lit k) = {} /\ ~s1.vs_call_ctx.cc_static` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all assign_base_storage_write_counted >>
  disch_then (qspecl_then [`g1`, `D`, `PG`] mp_tac) >> strip_tac >>
  qexistsl_tac [`g1`,
    `if tr then t1 with t_trans := key_update t1.t_trans k (op_taint t1 (Var tmp))
     else t1 with t_stor := key_update t1.t_stor k (op_taint t1 (Var tmp))`,
    `(if tr then tstore k (mload (w2n a) s) s1 else sstore k (mload (w2n a) s) s1)
      with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
      (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  Cases_on `tr` >> pure_rewrite_tac[ONE] >>
  pure_rewrite_tac[assign_base_store_prefix_suc, assign_base_store_prefix_zero,
    assign_base_store_frame_def, assign_base_store_taint_prefix_def] >>
  gvs[
    assign_base_store_frame_def, assign_base_store_taint_prefix_def,
    execution_frame_def, sstore_def, tstore_def, lookup_var_def,
    ptr_covers_def, op_taint_def, ADD1, WORD_ADD_0, WORD_MULT_CLAUSES]
QED

Theorem assign_base_storage_single_compiled_counted:
  !tr root k sa z sb fn s G tn ctx D PG a.
    (do loaded <- emit_op MLOAD [Var root];
        emit_void (if tr then TSTORE else SSTORE) [Lit k;loaded]
     od) sa = (z,sb) /\ fn_has_code sa sb fn /\ not_fresh_at sa root /\
    ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf u.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      execution_frame u = execution_frame
        (store_copy_prefix (if tr then LocTransient else LocStorage) a k s 1) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage) a k s tn 1 u tf /\
      ptr_covers Gf tf root u 32 /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_base_storage_single_shape >> strip_tac >>
  `root <> tmp /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id MLOAD [Var root] [tmp]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sa.cs_next_id+1) (if tr then TSTORE else SSTORE) [Lit k;Var tmp] [])` by
    (simp[EL_APPEND_EQN] >> metis_tac[ADD1]) >>
  drule_all assign_base_storage_single_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choose_then `gf` (qx_choose_then `tf` (qx_choose_then `u` strip_assume_tac))) >>
  qexistsl_tac [`gf`, `tf`, `u`] >> asm_rewrite_tac[] >> simp[] >> metis_tac[]
QED
