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
 * The external return's normalization, compile_return_normalize_frag, is in
 * exprSimTypedAlloc.
 *)

Theory stmtSimReturnWiden
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  list rich_list finite_map
  fragExec  exprSimAlloc exprSimCopy exprSimStorageCopy
  intCallReturnMem intCallResult typedMemoryCopy exprSimTypedAlloc valueCopy valueCopyBytes
  loweringSlice localPtrsProps stmtSimReturn
  stmtLowering exprLowering emitHelper exprLoweringProps context compileEnv loweringStateRelDefs
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

Theorem typed_return_empty_state_frame:
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
