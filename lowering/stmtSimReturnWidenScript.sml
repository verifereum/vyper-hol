(*
 * Returns whose value type widens to the declared return type
 *
 * type_stmt admits `return e` when expr_type e widens to the return type
 * (type_widens_to: a bytestring or dynamic array of a smaller bound,
 * elementwise).  The lowering passes both types on: an internal memory
 * return stores with compile_store_memory, which converts layouts with
 * compile_store_memory_typed; an external return first normalizes the value
 * into a fresh buffer of the return type with compile_store_memory_typed.
 *
 * TOP-LEVEL:
 *   stack_return_widens_eq — a stack-returned type only widens from itself
 *   compile_internal_return_memory_widen_frag — the memory return's store
 *     and RET for a value of a type that widens to the return type
 *   compile_return_normalize_frag — the external return's normalization:
 *     a fresh buffer holding the value at the return type's layout
 *)

Theory stmtSimReturnWiden
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  list rich_list finite_map
  fragExec  exprSimAlloc exprSimCopy exprSimStorageCopy
  intCallReturnMem intCallResult typedMemoryCopy exprSimTypedAlloc valueCopy valueCopyBytes
  loweringSlice localPtrsProps stmtSimReturn
  stmtLowering exprLowering emitHelper exprLoweringProps context compileEnv
  typedCopyDomain valueEncoding vyperTypeSystem vyperState vyperTyping
  venomExecSemantics venomInst venomState

Theorem stack_word_fits_eq[local]:
  (!sty ty. arg_type_fits sty ty /\ is_word_type ty ==> sty = ty) /\
  (!stys tys. arg_types_fit stys tys /\ EVERY is_word_type tys ==>
     stys = tys)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_word_type_def] >> gvs[]
QED

Theorem typed_return_empty_state_frame[local]:
  stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
  copy_static t = copy_static s /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!off len. off + len <= b \/ b + sz <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (cenv.ce_is_ctor ==> !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) b sz) /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==>
    lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx (es with scopes := []) t
Proof
  rpt strip_tac >> drule copy_static_fields >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor
     (es with scopes := []) t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     simp[] >> reverse conj_tac
     >- gvs[stmt_state_rel_def, state_rel_def] >>
     rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> simp[regions_disjoint_def]) >>
  rewrite_tac[stmt_state_rel_def] >> conj_tac
  >- (irule state_rel_frame >> conj_tac
      >- simp[local_ptrs_rel_def, local_region_def, lookup_scopes_def] >>
      qexistsl_tac [`es with scopes := []`, `s`] >>
      gvs[stmt_state_rel_def, state_rel_def, copy_static_def,
          venom_state_component_equality, local_ptrs_rel_def,
          local_region_def, lookup_scopes_def]) >>
  conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >>
               gvs[stmt_state_rel_def]) >>
  conj_tac >- (irule alloca_room_fields >> qexists_tac `s` >>
               gvs[stmt_state_rel_def]) >>
  conj_tac >- (irule fmp_room_fields >> qexists_tac `s` >>
               gvs[stmt_state_rel_def] >>
               qpat_x_assum `copy_static t = copy_static s` mp_tac >>
               simp[copy_static_def, venom_state_component_equality]) >>
  conj_tac >- (irule immutable_alloca_sep_fields >>
               qexistsl_tac [`s`, `es with scopes := []`] >>
               gvs[stmt_state_rel_def, local_region_def, lookup_scopes_def]) >>
  conj_tac >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
               gvs[stmt_state_rel_def]) >>
  gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
      local_region_def, lookup_scopes_def] >> first_assum ACCEPT_TAC
QED



(* Word members widen only from themselves, so stack returns need no
   conversion. *)
Theorem stack_return_widens_eq:
  !sft tenv sty ty.
    0 < returns_stack_count sft ty /\ type_widens_to tenv sty ty ==>
    sty = ty
Proof
  rpt gen_tac >> Cases_on `ty` >>
  simp[returns_stack_count_def, tuple_like_stack_count_def] >>
  rpt strip_tac >> gvs[COND_RAND, COND_RATOR, COND_EXPAND] >>
  metis_tac[typed_copy_word_widening, typed_copy_struct_widening,
            typed_copy_tuple_widening, cj 2 stack_word_fits_eq]
QED

Theorem return_bytestring_expr_rel:
  type_widens_to (get_tenv cx) sty ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\ value_has_type dtv v /\
  expr_val_rel cx sty v op s ==> expr_val_rel cx ty v op s
Proof
  rpt strip_tac >>
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  `~is_word_type sty /\ ~is_word_type ty` by
    metis_tac[is_bytestring_word_type] >>
  gvs[expr_val_rel_def] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED

(* compile_internal_return_memory_frag for a value of type sty stored at
   the return type ty.  The source region must not overlap the caller's
   buffer when the store converts layouts (compile_store_memory_typed).
   Intuition: word ty forces sty = ty (typed_copy_word_widening); a
   bytestring ty compiles as compile_store_memory at ty, and val_in_memory
   of BytesV/StringV doesn't depend on the bound; otherwise the typed copy
   (typed_copy_rank_entry) needs the gated disjointness clause. *)
Theorem compile_internal_return_memory_widen_frag:
  !ctx func cenv cx es ty sty dtv stv v val_op rpc elem_types buf_op sa sb bw.
    compile_internal_return cenv (SOME val_op) rpc 0 ty sty elem_types
      (SOME buf_op) sa = ((),sb) /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    (!x. buf_op = Var x ==> not_fresh_at sa x) /\
    (!x. rpc = Var x ==> not_fresh_at sa x) /\
    (!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    w2n bw + type_memory_size dtv + 64 < dimword (:256) /\
    (cenv.ce_is_ctor ==> !name itv iv off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
         SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name =
         SOME (itv,iv) ==>
       regions_disjoint off (type_memory_size itv) (w2n bw)
         (type_memory_size dtv)) ==>
    frag_exec ctx sa sb
      (\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
           expr_val_rel cx sty v val_op s /\
           eval_operand buf_op s = SOME bw /\
           (sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty ==>
            ?sw. eval_operand val_op s = SOME sw /\
                 w2n sw + type_memory_size stv < dimword (:256) /\
                 (w2n sw + type_memory_size stv <= w2n bw \/
                  w2n bw + type_memory_size dtv <= w2n sw)) /\
           ?pc. eval_operand rpc s = SOME pc)
      (\s. F)
      (intret_mem_q func cenv cx dtv bw v (es with scopes := []))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sty = ty`
  >- (gvs[] >> irule compile_internal_return_memory_frag >> simp[] >>
      metis_tac[]) >>
  `~is_word_type ty` by metis_tac[typed_copy_word_widening] >>
  Cases_on `is_bytestring_type ty`
  >- suspend "bytestring" >>
  suspend "compound"
QED

Resume compile_internal_return_memory_widen_frag[bytestring]:
  `compile_internal_return cenv (SOME val_op) rpc 0 ty ty elem_types
     (SOME buf_op) sa = ((),sb)` by
    (qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_internal_return_def, compile_store_memory_bytestring_src]) >>
  drule_all compile_internal_return_memory_frag >>
  disch_then (qspecl_then [`ctx`, `func`] assume_tac) >>
  drule frag_exec_weaken >> disch_then irule >> simp[] >>
  rpt strip_tac >> simp[] >>
  irule return_bytestring_expr_rel >> metis_tac[]
QED

Resume compile_internal_return_memory_widen_frag[compound]:
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_ignore_bind_def, comp_bind_def,
       compile_store_memory_def] >>
  Cases_on `compile_store_memory_typed cenv buf_op ty val_op sty sa` >>
  rename1 `compile_store_memory_typed _ _ _ _ _ _ = (u,sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  `cs_extends sa sm` by
    (drule typed_return_store_mono >> simp[ci_mono_def]) >>
  `cs_extends sm sb` by (irule cs_extends_emit_inst >> metis_tac[]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. stmt_state_rel ctx func cenv cx (es with scopes := []) s /\
    val_in_memory dtv v (w2n bw) s.vs_memory /\
    ?pc. eval_operand rpc s = SOME pc`, `sm`] >> simp[] >>
  conj_tac
  >- suspend "typed_store" >>
  irule emit_ret_pc_frag >> qexists_tac `rpc` >> simp[] >>
  rpt strip_tac >>
  gvs[intret_mem_q_def, intret_q_def, result_rel_def,
      intret_vals_match_def, stmt_state_rel_def]
QED

Resume compile_internal_return_memory_widen_frag[typed_store]:
  `~is_word_type sty` by metis_tac[return_source_word_widens_eq] >>
  irule frag_exec_pointwise >> rpt strip_tac >>
  gvs[] >> (
  `val_in_memory stv v (w2n sw) s0.vs_memory` by
    gvs[expr_val_rel_def] >>
  drule typed_return_store_frag >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `sfields_tenv_consistent _ _`)) >>
  disch_then (drule_at (Pat `eval_operand buf_op _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ty = _`)) >>
  disch_then (qspecl_then [`bw`, `dtv`] mp_tac) >>
  disch_then (qspecl_then [`ctx`,
    `intret_mem_q func cenv cx dtv bw v (es with scopes := [])`,
    `\t. stmt_state_rel ctx func cenv cx (es with scopes := []) t`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      `!x. cenv.ce_imm_alloca = SOME (Var x) ==>
           lookup_var x t = lookup_var x s0` by metis_tac[] >>
      irule typed_return_empty_state_frame >>
      qexistsl_tac [`w2n bw`, `s0`, `type_memory_size dtv`] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >>
          simp[arithmeticTheory.ADD_COMM]) >>
      first_assum ACCEPT_TAC) >>
  disch_then assume_tac >> drule frag_exec_weaken >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  qexists_tac `pc` >>
  drule copy_static_fields >> strip_tac >> Cases_on `rpc` >>
  gvs[eval_operand_def, lookup_var_def])
QED

Finalise compile_internal_return_memory_widen_frag
