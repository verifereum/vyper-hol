(* The materializer's observed endpoint and its independent native cut. *)
Theory entryCreateIfExpArm
Ancestors
  bodyFullIfExpPrepare entryCreateIfExpArmCompose entryCreateIfExpArmVisit
  entryCreateIfExpTypedObserverCode entryCreateIfExpTypedObserverPath
  entryCreateIfExpUnwrapObserve emitHelperProps exprLoweringProps fragFuel
  entryCreatePathScope createSizeCutCode fragExec bodyFullIfExpObserve list
  venomExecProofs abiEncoderProps

Triviality ifexp_typed_store_scoped:
  ifexp_observed_typed_store (ifexp_arm_scope E)
Proof
  mp_tac ifexp_typed_store_observation_from_install >> impl_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all ifexp_typed_store_observer_code >> strip_tac >>
      qexists_tac `id` >> asm_rewrite_tac [] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!i l. _` (drule_all_then strip_assume_tac) >>
      asm_rewrite_tac [] >> metis_tac[]) >>
  pure_rewrite_tac [ifexp_observed_typed_store_def] >> strip_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!explicit PG. ?t Gf tnf. _`
    (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t`,`Gf`,`tnf`] >>
  fs[ifexp_arm_scope_def, ifexp_arm_guard_def, no_phi_fn_def, EVERY_MEM] >> gvs[]
QED

Triviality ifexp_unwrap_scoped:
  ifexp_observed_unwrap T (ifexp_arm_scope E) DF lo E C f PG d ce cx
Proof
  mp_tac (Q.INST [`guard` |-> `ifexp_arm_guard f`, `obs` |-> `ifexp_arm_scope E`,
                  `explicit` |-> `E`, `ctx` |-> `C`, `func` |-> `f`, `cenv` |-> `ce`]
                 ifexp_owned_unwrap_observation) >>
  impl_tac >- (simp[ifexp_arm_scope_def, ifexp_arm_guard_def] >>
                metis_tac[lookup_block_MEM]) >>
  simp[]
QED

Triviality ifexp_arm_guard_at_assign:
  create_layout a b /\
  (!bb. MEM bb f.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  emit_inst ASSIGN [op] [rv] b = ((),sy) /\ fn_has_code b sy f ==>
  ifexp_arm_guard f a b
Proof
  strip_tac >> simp[ifexp_arm_guard_def] >> rpt strip_tac >>
  `create_cut_code {} b sy` by
    (`create_cut_code {} b (SND (emit_inst ASSIGN [op] [rv] b))` suffices_by simp[] >>
     irule create_cut_code_emit_inst >> simp[create_cut_targets_def]) >>
  drule emit_inst_extends >> strip_tac >>
  `LENGTH b.cs_current_insts <> LENGTH sy.cs_current_insts` by simp[] >>
  `b.cs_next_id <= i.inst_id` by metis_tac[create_cut_continuation_fetch] >>
  fs[frag_ids_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ifexp_selected_materialization_site:
  create_layout sm sb /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  emit_inst ASSIGN [op] [rv] sb = ((),sy) /\ fn_has_code sb sy func /\
  compile_expr cenv ty e sa = (vv,sm) /\
  (is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) vv sm = (op,sb) /\
  (post_value_type cenv e = t /\
   (is_word_type t \/
    same_memory_layout cenv (lowered_value_type cenv e) t /\
    (?rtp. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rtp) \/
    ~same_memory_layout cenv (lowered_value_type cenv e) t /\
    is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) t) \/
   ~is_word_type t /\ ~same_memory_layout cenv (lowered_value_type cenv e) t /\
   post_value_type cenv e = lowered_value_type cenv e /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv) \/
   ~is_word_type t /\ post_value_type cenv e <> t /\
   post_value_type cenv e = lowered_value_type cenv e /\
   same_memory_layout cenv (lowered_value_type cenv e) t /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
   (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv)) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (e = a \/ e = b) /\ expr_type e = t /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  (!v. read_result cx tva ee = (INL v,ee) ==>
     value_has_type rty v /\
     !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
       value_has_type ptv v) /\
  MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
  (!id path. tva = PlaceR (MemoryPlace id path) ==>
    same_memory_layout cenv (lowered_value_type cenv e) t) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  eval_result_typed (env,cx,ee) tva (Type (expr_type e)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx e es1 sa sm u ee tva vv z /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tva vv z /\
  z.vs_current_bb = sm.cs_current_bb /\
  z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
  alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
  (!v. tva = Value v /\ ~is_word_type (post_value_type cenv e) /\
    ~is_bytestring_type (post_value_type cenv e) ==>
    vv_own cenv cx (post_value_type cenv e) sa sm ee tva vv z) /\
  ptr_vv_ok cx (post_value_type cenv e) tva vv ee G tn z /\
  (!t' op0. vv = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
     ptr_buf_ok cenv e op0 G z) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G z) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tva ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) z = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es1 sa G1 tn1 u G tn ==>
  ?v z' Gz tf.
    create_operand_at sm z /\
    create_operand_full_scope sm sb explicit ctx func z [] (OK z') /\
    read_result cx tva ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (z, G, tn) [] (OK z', Gz, tf) /\
       expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
       ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
    (~is_word_type t ==>
     vv_at cenv cx t sa sb ee tva (LocatedValue t (mk_ptr op LocMemory)) z') /\
    (~is_word_type t ==> !id path. tva = PlaceR (MemoryPlace id path) ==>
      vv_place_ptr cenv cx ee z' tva (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v. conditional_result cx tva ee = (INL ctv,ee) /\
      ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own cenv cx t sa sb ee ctv
        (LocatedValue t (mk_ptr op LocMemory)) z') /\
    expr_store_bound cx t v op z' /\
    z'.vs_current_bb = sb.cs_current_bb /\
    z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
    ptr_val_ok cx t v op Gz tf z' /\
    (~is_word_type t ==>
     !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
    (~is_word_type t ==>
     !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/
            w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
    ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ifexp_arm_guard_at_assign >> disch_tac >>
  mp_tac (Q.INST [`obs` |-> `ifexp_arm_scope explicit`] ifexp_selected_arm_step_observed) >>
  impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, irule ifexp_unwrap_scoped,
           irule ifexp_alloc_observed_scoped, irule ifexp_bytes_observed_scoped,
           irule ifexp_typed_store_scoped, irule ifexp_widening_observed_scoped]) >>
  simp[ifexp_arm_scope_def] >> metis_tac[]
QED
