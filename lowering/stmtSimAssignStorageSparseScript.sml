(* Assignment to a top-level storage or transient variable of an
   ABI-dynamic type: a struct, tuple or static array with a nested DynArray
   or bytestring part.  The lowering stores only the live slots
   (compile_store_slots), and placeStoreSlots' place_store_slots_suffix_run
   proves that store.  stmtSimAssignStorageCopy has the ABI-static case. *)

Theory stmtSimAssignStorageSparse
Ancestors
  stmtSimAssignStorageCopy vyperStorageBackend placeStoreSlots exprSimHash exprSimHashBoundary exprOpenPrimitives
  exprSimTopLevelProps stmtSimAssignStorage
  stmtSimDeclMem
  gasOutcome stmtSimProps stmtSimForced exprSimProps stmtSimDefs exprSimDefs
  loweringPosts fragExec exprOperandVar stmtSimAssignStorage
  exprLowering stmtLowering emitHelper exprLoweringProps context compileEnv loweringStateRelDefs
  stmtLoweringMono vyperContext vyperAST vyperInterpreter vyperState
  vyperStorage vyperValue vyperTyping vyperStorageLayoutSafety
  vyperStoragePlaceRegion venomExecSemantics venomInst venomState
  valueEncoding list
Libs
  monadsyntax

Theorem mem_to_slots_open[local]:
  !b src slot w s u t.
    (if b then compile_memory_to_transient else compile_memory_to_storage)
      src slot w s = (u,t) ==>
    ~block_is_terminated t
Proof
  Cases >>
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def,
       compile_word_copy_loop_def] >>
  metis_tac[word_copy_loop_op_open]
QED

Theorem emit_void_store_open[local]:
  !b args s u t.
    emit_void (if b then TSTORE else SSTORE) args s = (u,t) ==>
    ~block_is_terminated t
Proof
  rpt strip_tac >> drule emit_void_terminated >> Cases_on `b` >>
  simp[is_terminator_def]
QED

Theorem copy_elements_open[local]:
  !cenv src slot elem cnt tr s u t.
    compile_copy_elements_to_slots cenv src slot elem cnt tr s = (u,t) ==>
    ~block_is_terminated t
Proof
  rpt gen_tac >>
  simp[Once compile_store_slots_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[new_block_def, block_is_terminated_def]
QED

(* An ABI-dynamic type that is not a bytestring is an array, or a tuple or
   struct with members. *)
Theorem abi_dynamic_shape[local]:
  !sf ty.
    is_abi_dynamic sf ty /\ ~is_bytestring_type ty ==>
    (?elem bd. ty = ArrayT elem bd) \/
    (?tys. ty = TupleT tys /\ tys <> []) \/
    (?nsid fields. ty = StructT nsid /\
       FLOOKUP sf (nsid_to_string nsid) = SOME fields /\ fields <> [])
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[is_abi_dynamic_def, is_bytestring_type_def]
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> simp[is_abi_dynamic_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      simp[is_abi_dynamic_def, is_bytestring_type_def])
  >- (rename1 `EXISTS _ tys` >> Cases_on `tys` >> simp[]) >>
  CASE_TAC >> simp[] >> rename1 `MAP _ fields` >> Cases_on `fields` >> simp[]
QED

(* The live-slot store leaves its block open.  The members of an
   ABI-dynamic tuple or struct are not empty. *)
Theorem store_slots_open:
  (!cenv src slot ty tr s u t.
     compile_store_slots cenv src slot ty tr s = (u,t) /\
     acyclic_struct_metadata cenv.ce_struct_fields ==>
     ~block_is_terminated t) /\
  (!cenv src slot members mem_off slot_off tr s u t.
     compile_store_slots_members cenv src slot members mem_off slot_off tr s =
       (u,t) /\
     acyclic_struct_metadata cenv.ce_struct_fields /\
     (members = [] ==> ~block_is_terminated s) ==>
     ~block_is_terminated t) /\
  (!cenv src slot elem cnt tr s u t.
     compile_copy_elements_to_slots cenv src slot elem cnt tr s = (u,t) ==>
     ~block_is_terminated t)
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac >> rpt strip_tac
  >- (qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
      simp_tac std_ss [Once compile_store_slots_def, LET_THM] >>
      IF_CASES_TAC
      >- (IF_CASES_TAC >>
          simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          metis_tac[emit_void_store_open, mem_to_slots_open]) >>
      IF_CASES_TAC
      >- (simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          metis_tac[word_copy_loop_op_open]) >>
      IF_CASES_TAC >- gvs[] >>
      `is_abi_dynamic cenv.ce_struct_fields ty` by gvs[] >>
      drule_all abi_dynamic_shape >> strip_tac >> gvs[]
      >- (Cases_on `bd` >>
          simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
          metis_tac[emit_void_store_open, copy_elements_open])
      >- (strip_tac >> first_x_assum drule >> simp[])
      >- (strip_tac >> first_x_assum drule >> gvs[get_struct_fields_def]))
  >- gvs[Once compile_store_slots_def, comp_return_def]
  >- (qpat_x_assum `compile_store_slots_members _ _ _ (_::_) _ _ _ _ = _`
        mp_tac >>
      simp[Once compile_store_slots_def, comp_bind_def,
           comp_ignore_bind_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> metis_tac[])
  >- metis_tac[copy_elements_open]
QED
(* Assignment to a non-word storage or transient variable with no length
   word, by the live-slot store.  The region fits the slot space. *)
Theorem compile_assign_storage_sparse_stmt_frag:
  !ctx func cx lctx RetQ cenv ty src id e es ts tr typ id_str slot tvt env.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    expr_type e = typ /\ lowered_value_type cenv e = expr_type e /\
    ~is_word_type typ /\ ~is_bytestring_type typ /\ ~has_length_word typ /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    0 < type_slot_size tvt /\
    type_memory_bytes cenv typ = type_memory_size tvt /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME typ /\
    slot + type_slot_size tvt <= dimword (:256) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    (!gs v es1.
       (do result <- eval_expr cx e; read_result cx result od)
         (es with gas_obs := gs) = (INL v, es1) ==>
       value_has_type tvt v /\ expr_sim_inv cenv cx env es1) /\
    expr_sim ctx func cenv cx (expr_type e) e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget (src, id))) e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `~(has_length_word (expr_type e) /\ is_empty_value_expr e)` by simp[] >>
  drule_all assign_storage_copy_code_parts >> strip_tac >> gvs[] >>
  fs[] >>
  `cs_extends sa sB` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sB sb` by
    metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa sB func /\ fn_has_code sB sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all eval_assign_toplevel_action >>
  disch_then (qspec_then `e` assume_tac) >>
  irule forced_then_stmt_outcome >>
  qexistsl_tac [
    `\v ee t. expr_post ctx func cenv cx e es sa sB s0 ee v op t /\
              t.vs_current_bb = sB.cs_current_bb /\
              t.vs_inst_idx = LENGTH sB.cs_current_insts`,
    `e`, `write_storage_slot cx tr (n2w slot) tvt`] >>
  reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `expr_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `sB`, `op`, `s0`] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[forced_then_admissible]) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `value_has_type tvt v /\ expr_sim_inv cenv cx env ee` by
    (qpat_x_assum `!gs v es1. _ ==> _ /\ _` irule >>
     fs[ETA_THM] >> metis_tac[]) >>
  `~cx.txn.is_static` by fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  drule typed_storage_copy_write >>
  disch_then (qspecl_then [`cx`, `tr`, `n2w slot`, `ee`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_lowered >> first_assum ACCEPT_TAC) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `expr_val_rel cx (expr_type e) v op t` by
    (qpat_x_assum `expr_val_rel _ (post_value_type _ _) _ _ _` mp_tac >>
     simp[]) >>
  `?sw. eval_operand op t = SOME sw /\
        val_in_memory tvt v (w2n sw) t.vs_memory` by
    (qpat_x_assum `expr_val_rel _ (expr_type _) _ _ _` mp_tac >>
     simp[expr_val_rel_def] >> strip_tac >> qexists_tac `w` >> simp[]) >>
  `w2n sw + val_footprint tvt v < dimword (:256)` by
    (drule_all hash_post_footprint_bound >> simp[]) >>
  `val_footprint tvt v = type_memory_size tvt` by
    metis_tac[topcopy_val_footprint] >>
  `w2n sw + type_memory_size tvt < dimword (:256)` by
    (qpat_x_assum `val_footprint _ _ = _` (SUBST_ALL_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `compile_store_slots cenv op (Lit (n2w slot)) (expr_type e) tr sB =
     ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `tr` >>
     simp[stmtLoweringTheory.compile_assign_value_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def]) >>
  `sa.cs_next_var <= sB.cs_next_var /\ sa.cs_next_id <= sB.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sB x` by
    metis_tac[compile_lower_value_var] >>
  `~t.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `slot < dimword (:256)` by decide_tac >>
  qspecl_then [`cenv`, `op`, `Lit (n2w slot)`, `expr_type e`, `tr`, `sB`, `sb`,
    `tvt`, `func`, `t`, `sw`, `slot`, `ctx`, `cx`, `env`, `ee`, `src`, `id`,
    `[]`, `n2w slot`, `tvt`, `[]`, `0`, `writes`, `v`] mp_tac
    place_store_slots_suffix_run >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[eval_operand_def, storage_subregion_def]) >>
  strip_tac >>
  `~block_is_terminated sb` by
    (drule_all (cj 1 store_slots_open) >> simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t' = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sB x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
        simp[ci_mono_def]) >>
     metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t'.vs_allocas aid = SOME b` by metis_tac[] >>
  qabbrev_tac `ee' = set_storage cx ee tr
    (apply_writes (n2w slot) writes (get_storage cx ee tr))` >>
  `ee'.gas_obs = []` by (Cases_on `tr` >> simp[Abbr `ee'`, set_storage_def]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  qexistsl_tac [`INL ()`, `ee'`, `OK t'`] >>
  conj_tac >- fs[write_storage_slot_gas_obs] >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl]
QED
