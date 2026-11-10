Theory bodyImmutableAugAssignPaths
Ancestors
  bodyImmutableAugAssignFacts bodyImmutableAugAssignStore bodySim exprSimHypsDefs
  stmtSimAugAssignStorage stmtSimAugAssign exprOpenPrimitives stmtSimProps
  venomInst vyperState vyperInterpreter stmtSimDeclPath
  stmtLowering exprLowering exprLoweringProps emitHelper emitHelperProps
  stmtSimDefs compileEnv loweringStateRelDefs loweringPosts exprSimMemoryPath fragGasMode
  venomState freshWrites finite_map localPtrsProps

Theorem immutable_augassign_code_parts:
  stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) sa = (c,sf) /\
  FLOOKUP cenv.ce_module_vars nsid = SOME (ImmutableLoc off) ==>
  c = cenv /\
  ?s1 s2 s3 cur_op rhs_op res_op.
    emit_op MLOAD [Lit (n2w off)] sa = (cur_op,s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs_op,s2) /\
    compile_binop bop cur_op rhs_op ty NONE
      (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op,s3) /\
    emit_void MSTORE [Lit (n2w off);res_op] s3 = ((),sf)
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def,declare_stmt_local_def,compile_stmt_def,
       compile_get_target_ptr_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def] >>
  Cases_on `emit_op MLOAD [Lit (n2w off)] sa` >> rename1 `_ = (cur_op,s1)` >> simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >> rename1 `_ = (rhs_op,s2)` >> simp[] >>
  Cases_on `compile_binop bop cur_op rhs_op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `_ = (res_op,s3)` >> simp[] >>
  Cases_on `emit_void MSTORE [Lit (n2w off);res_op] s3` >> simp[oneTheory.one]
QED

Theorem immutable_augassign_load_frame:
  emit_op MLOAD [Lit (n2w off)] sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ off < dimword (:256) /\
  mload off s0 = word ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\ eval_operand op t = SOME word /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
      (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
      t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
      t.vs_memory = s0.vs_memory /\
      (?out. op = Var out /\ not_fresh_at sb out)
Proof
  strip_tac >>
  `eval_operand (Lit (n2w off)) s0 = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all emit_mload_marked_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var)) word s0)
    with vs_inst_idx := SUC s0.vs_inst_idx` >>
  conj_tac >- gvs[wordsTheory.w2n_n2w] >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
      simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     gvs[emit_op_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
         fresh_var_def,fresh_id_def,emit_def]) >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
       fresh_var_def,fresh_id_def,emit_def] >> strip_tac >> gvs[] >>
  simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE,not_fresh_at_def,eval_operand_def]
QED

(* An MSTORE into a constructor immutable's word keeps every alloca's
   bytes: immutable_decl_sep separates the immutable from every alloca. *)
Theorem immutable_mstore_alloca_frame[local]:
  alloca_frame c0 e0 sa s0 cenv ee s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
  stmt_state_rel ctx func cenv cx ee s /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_size tv = 32 /\
  ee1.scopes = ee.scopes ==>
  alloca_frame c0 e0 sa s0 cenv ee1 (mstore off w s with vs_inst_idx := k)
Proof
  strip_tac >>
  `immutable_decl_sep cenv cx ee.scopes s.vs_vars s.vs_allocas
     s.vs_alloca_next` by
    fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
  fs[immutable_decl_sep_alt] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[alloca_frame_def] >> rpt strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac)
  >- (`FLOOKUP s.vs_allocas aid = SOME (off',sz)` by metis_tac[] >>
      `regions_disjoint off 32 off' sz` by metis_tac[] >>
      fs[regions_disjoint_def] >>
      simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]) >>
  first_x_assum irule >>
  gvs[local_region_def, mstore_def, lookup_var_def] >> metis_tac[]
QED

Theorem immutable_augassign_store_post_path:
  emit_void MSTORE [Lit (n2w off); op] st = ((),sf) /\
  fn_has_code st sf func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME ty /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  value_has_type tv w /\ off < dimword (:256) /\
  eval_operand op s = SOME (typed_val_to_w256 tv w) /\
  (!x wd. not_fresh_at sa x /\ lookup_var x s0 = SOME wd ==>
          lookup_var x s = SOME wd) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv ee s ==>
  ?fin last. write_place cx (ImmutablePlace cenv.ce_module id []) w ee =
      (INL (),fin) /\
    gas_marked_path F ctx func s 0 (OK last) /\
    stmt_post ctx func cx lctx cenv cenv sa sf es s0 (INL ()) fin last
Proof
  strip_tac >>
  drule_all immutable_augassign_entry >> strip_tac >> gvs[] >>
  drule_all immutable_augassign_write_source >> strip_tac >>
  `?fin. write_place cx (ImmutablePlace cenv.ce_module id []) w ee =
     (INL (),fin)` by metis_tac[] >>
  drule_all immutable_augassign_store >> strip_tac >>
  `gas_marked_path F ctx func s 0
    (OK (mstore off (typed_val_to_w256 tv w) s with
           vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[Lit (n2w off);op]`, `MSTORE`, `[]`, `st`, `sf`] >>
     gvs[emit_void_def, emit_inst_def, is_terminator_def] >>
     `off = w2n (n2w off : 256 word)` by simp[wordsTheory.w2n_n2w] >>
     pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     irule step_MSTORE >> simp[eval_operand_def]) >>
  `sf.cs_current_bb = st.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH st.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> simp[is_terminator_def]) >>
  `fin.scopes = ee.scopes` by
    (qpat_x_assum `write_place _ _ _ _ = (INL (),fin)` mp_tac >>
     asm_rewrite_tac[] >> rw[] >> simp[]) >>
  `cenv.ce_is_ctor` by fs[body_inv_def] >>
  `type_memory_size tv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `alloca_frame cenv es sa s0 cenv fin
     (mstore off (typed_val_to_w256 tv w) s with
        vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule immutable_mstore_alloca_frame >> simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ ee s` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  gvs[mstore_def, lookup_var_def]
QED
