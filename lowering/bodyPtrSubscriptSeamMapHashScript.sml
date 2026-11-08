(* Consumer boundary for the complete mapping-slot hash suffix. *)
Theory bodyPtrSubscriptSeamMapHash
Ancestors
  bodyPtrSubscriptSeamMapSuffix bodyPtrSubscriptSeamMapRuntime
  bodyPtrSubscriptSeamMapFrame bodyPtrHashBuiltinsGhostFrame
  exprSimMapKey exprSimProps loweringPosts bodyPtrDefs
  venomState ptrDiscipline compileEnv exprLoweringProps finite_map pred_set

Theorem mapping_slot_hash_ptr_frame:
  !D ctx fn PG G tn s bb slot key sa op sb w0 w1 cenv cx es d.
    compile_mapping_subscript slot key sa = (op,sb) /\
    (!z. slot = Var z \/ key = Var z ==> not_fresh_at sa z) /\
    eval_operand slot s = SOME w0 /\ eval_operand key s = SOME w1 /\
    op_taint tn slot = {} /\ op_taint tn key = {} /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?t G' tn'. run_inst_seq (emitted_insts sa sb) s = OK t /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      eval_operand op t = SOME (hashmap_slot w0 w1) /\
      t.vs_current_bb = s.vs_current_bb /\ stmt_state_rel ctx fn cenv cx es t /\
      ghost_inv d cenv cx es G' tn' t /\
      ghost_inv d cenv cx es G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      ghost_kept cenv es sa G tn s G' tn' /\
      op_taint tn' op = {} /\ op_prov G' op = NONE /\
      wb_frame cenv es sa s t /\
      (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s /\
        FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  rpt gen_tac >> strip_tac >>
  `(!z. slot = Var z ==> not_fresh_at sa z) /\
   (!z. key = Var z ==> not_fresh_at sa z)` by metis_tac[] >>
  drule_all compile_mapping_subscript_run >> strip_tac >>
  drule_all mapping_slot_hash_counted >>
  disch_then (qspecl_then [`D`, `PG`, `G`] strip_assume_tac) >>
  drule_all mapping_slot_hash_runtime_fields >> strip_tac >>
  `stor_taint_ok cx tn' t` by gvs[stor_taint_ok_def, ghost_inv_def] >>
  `ghost_inv d cenv cx es G' tn' t` by
    (irule hash_ghost_inv_region_frame >> simp[] >>
     qexistsl [`G`, `ctx`, `fn`, `s`, `sa`, `tn`] >> simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G tn s G' tn'` by
    (irule hash_ghost_kept_frame >> gvs[SUBSET_DEF] >> metis_tac[]) >>
  `wb_frame cenv es sa s t` by
    (simp[wb_frame_def] >> conj_tac >- metis_tac[] >>
     irule locals_kept_regions >> metis_tac[]) >>
  qexistsl [`t`, `G'`, `tn'`] >> simp[hash_ghost_inv_inst_idx] >> metis_tac[]
QED
