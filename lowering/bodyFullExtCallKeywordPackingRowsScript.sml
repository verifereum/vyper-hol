(* Saved positional operands at the physical exit of successful keywords. *)
Theory bodyFullExtCallKeywordPackingRows
Ancestors
  bodyFullExtCallPosTransport bodyFullExtCallSavedOperand
  exprSimProps stateRelProj freshWrites loweringPosts bodyPtrDefs
  exprLoweringProps context vyperStorageFootprint vyperStorageBackend vyperState list
  wordArgsPtr exprSimHypsDefs exprLowering compileEnv typedMemoryCopy

(* The positional snapshot owns only IDs and variables already old at the
   keyword entry. Restrict the frame, not the value's compiler interval. *)
Theorem keyword_packing_restrict_frame[local]:
  ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
  wb_frame cenv pos ee sb u t /\
  ghost_kept_at lo cenv pos sb Gp tp u G tn /\
  (!x w. not_fresh_at sb x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) ==>
  wb_frame cenv pos ee ss u t /\
  ghost_kept_at lo cenv pos ss Gp tp u G tn /\
  (!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w)
Proof
  strip_tac >>
  `!x. not_fresh_at ss x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  rpt conj_tac
  >- (qpat_assum `wb_frame _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
      rewrite_tac[wb_frame_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rpt strip_tac >> metis_tac[]) >>
      qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
      `aid < sb.cs_next_id` by decide_tac >>
      qpat_assum `!aid off sz. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[])
  >- (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
      rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rpt strip_tac >> metis_tac[]) >>
      qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
      `aid < sb.cs_next_id` by decide_tac >>
      qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  metis_tac[]
QED

Theorem keyword_packing_endpoint_frame[local]:
  stmt_state_rel H ctx func cenv cx pos u /\
  stmt_state_rel H ctx func cenv cx ee t /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM ee.scopes = MAP FDOM pos.scopes /\
  wb_frame cenv pos ee sb u t ==>
  alloca_inv u /\ alloca_inv t /\
  (!n b sz. local_region cenv pos.scopes u n b sz <=>
             local_region cenv ee.scopes t n b sz)
Proof
  strip_tac >>
  `MAP FDOM pos.scopes = MAP FDOM ee.scopes` by simp[] >>
  drule_all wordArgsPtrTheory.wb_frame_local_regions >>
  metis_tac[stmt_state_rel_local_ptrs_alloca]
QED

(* This is a one-horizon row. The selected witness serves the dynamic
   conjuncts; storage liveness can subsequently be projected at any horizon. *)
Theorem keyword_packing_row_endpoint[local]:
  !mods.
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)
    sm = (sv,ss) /\
  (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
    ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
      eval_operand (vv_operand sv) u = SOME w /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      val_wf tv v /\ FLOOKUP u.vs_allocas sm.cs_next_id =
        SOME (w2n w,type_memory_size tv) /\
      si.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < ss.cs_next_id /\
      (!n b len. local_region cenv pos.scopes u n b len ==>
         regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
  ((?tag op0. sv = StackValue tag op0) \/
   (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
        ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
   (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
        ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
        lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
  (?raw. read_result cx raw pos = (INL v,pos) /\
         vv_holds cenv cx (lowered_value_type cenv e) raw sv pos u /\
         vv_at cenv cx (lowered_value_type cenv e) si ss pos raw sv u /\
         ptr_vv_ok cx (lowered_value_type cenv e) raw sv pos Gp tp u /\
         vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) pos raw sv u) /\
  vv_storage_live (H:(bool # bytes32 # type_value) list # num list) cx sv pos u /\
  (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
    ptr_buf_ok cenv e op Gp u) /\
  (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand Gp u) /\
  (!x. vv_operand sv = Var x ==> not_fresh_at ss x) /\
  wb_frame cenv pos ee ss u t /\
  ghost_kept_at lo cenv pos ss Gp tp u G tn /\
  (!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  u.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = u.vs_labels /\
  alloca_inv u /\ alloca_inv t /\
  (~copy ==> ee.scopes = pos.scopes /\ ee.immutables = pos.immutables /\
     (!tr. get_storage cx ee tr = get_storage cx pos tr)) /\
  (!n b sz. local_region cenv pos.scopes u n b sz <=>
             local_region cenv ee.scopes t n b sz) /\
  stmt_state_rel H ctx func cenv cx pos u /\
  stmt_state_rel H ctx func cenv cx ee t /\
  local_ptrs_reserved cenv ss /\ expr_sim_inv_mods mods cenv cx env pos /\
  ghost_inv_at D lo d cenv cx ee G tn t /\ dead_lo_ok H D lo cenv cx ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
         vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
         vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
         ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
         vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
  vv_storage_live H cx sv ee t /\
  ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
    | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok cenv e (vv_operand sv) G t)
Proof
  namedCases_on `sv` ["tag op", "tag p"] >>
  simp[vv_operand_def, vv_location_def, Excl "vv_storage_live_def"] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (simp[vv_storage_live_def] >> irule extcall_request_saved_stack_endpoint >>
      simp[ci_mono_refl] >> qexistsl_tac [`Gp`,`func`,`lo`,`pos`,`ss`,`u`,`tp`] >>
      Cases_on `is_word_type (lowered_value_type cenv e)` >>
      simp[ci_mono_refl] >>
      `~copy` by metis_tac[] >>
      disj2_tac >> qexistsl_tac [`env`,`H`,`H`,`ctx`] >> simp[]) >>
  `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `_ \/ _` mp_tac >> metis_tac[]) >>
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qpat_x_assum `_ \/ _` kall_tac >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `copy`
      >- (qpat_assum `_ ==> ?x w tv. p.ptr_location = LocMemory /\ p.ptr_operand = Var x /\ _` mp_tac >>
          impl_tac >- simp[] >>
          disch_then (qx_choosel_then [`x`,`w`,`tv`] strip_assume_tac) >>
          `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
             lowered_value_type cenv e` by
            (Cases_on `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` >>
             qpat_x_assum `compile_snapshot_vv cenv T _ sm = _` mp_tac >>
             simp[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
             pairarg_tac >> simp[]) >>
          `ptr_val_ok cx (lowered_value_type cenv e) v (Var x) Gp tp u /\
           val_in_memory tv v (w2n w) u.vs_memory` by
            (qpat_assum `?raw. read_result cx raw pos = (INL v,pos) /\ _`
               (qx_choose_then `raw0` strip_assume_tac) >>
             gvs[vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def]) >>
          `lookup_var x u = SOME w` by
            (qpat_assum `p.ptr_operand = Var x` (fn eq =>
               qpat_assum `eval_operand p.ptr_operand u = SOME w`
                 (ACCEPT_TAC o REWRITE_RULE [eq, venomStateTheory.eval_operand_def]))) >>
          `w2n w + type_memory_size tv <= u.vs_alloca_next` by
            (irule allocaSiteResourceTheory.alloca_site_registered_below >> simp[] >>
             qexists_tac `sm.cs_next_id` >> simp[]) >>
          `ptr_buf_ok cenv e (Var x) Gp u` by
            (qpat_assum `p.ptr_operand = Var x` (fn eq =>
               qpat_assum `p.ptr_location = LocMemory` (fn loc =>
                 qpat_assum `_ ==> ptr_buf_ok cenv e p.ptr_operand Gp u`
                   (ACCEPT_TAC o REWRITE_RULE [eq] o C MP loc)))) >>
          mp_tac (Q.INST [`cenv` |-> `cenv`, `e` |-> `e`, `cut` |-> `ss`,
             `a` |-> `sm`, `si` |-> `si`, `ss` |-> `ss`,
             `mid` |-> `pos`, `ee` |-> `ee`, `t` |-> `u`, `u` |-> `t`,
             `G1` |-> `Gp`, `G2` |-> `G`, `tn1` |-> `tp`, `tn2` |-> `tn`,
             `input` |-> `ext_call_arg_value (lowered_value_type cenv e) vv`,
             `saved` |-> `LocatedValue (lowered_value_type cenv e) p`,
             `x` |-> `x`, `w` |-> `w`, `tv` |-> `tv`, `aid` |-> `sm.cs_next_id`,
             `sz` |-> `type_memory_size tv`, `lo` |-> `lo`, `cx` |-> `cx`,
             `v` |-> `v`] extcall_request_materialized_endpoint) >>
          simp[vv_operand_def, vv_storage_live_def, exprSimPropsTheory.val_footprint_le,
               loweringStateRelDefsTheory.regions_disjoint_def] >>
          impl_tac
          >- (rpt strip_tac >>
              `local_region cenv pos.scopes u n b len` by
                (qpat_assum `!n b sz. local_region cenv pos.scopes u n b sz <=> _`
                   (qspecl_then [`n`,`b`,`len`] mp_tac) >> simp[]) >>
              qpat_assum `!n b len. local_region cenv pos.scopes u n b len ==> _`
                (drule_then (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
              decide_tac) >>
          strip_tac >> simp[] >> qexists_tac `Value v` >> simp[]) >>
      fs[vv_storage_live_def] >> irule extcall_request_saved_memory_endpoint >> simp[] >>
      qexistsl_tac [`Gp`,`func`,`lo`,`pos`,`ss`,`u`,`tp`] >>
      simp[ci_mono_refl] >> conj_tac >- (qexists_tac `raw` >> simp[]) >>
      disj2_tac >> qexistsl_tac [`env`,`H`,`H`,`ctx`] >> simp[]) >>
  `~copy` by metis_tac[] >>
  Cases_on `?tr. p.ptr_location = slot_loc tr`
  >- (qpat_x_assum `?tr. p.ptr_location = slot_loc tr` (qx_choose_then `tr` assume_tac) >>
      simp[Excl "vv_storage_live_def"] >> irule extcall_request_saved_slot_endpoint >>
      simp[Excl "vv_storage_live_def"] >> conj_tac
      >- (qexistsl_tac [`ctx`,`func`] >> simp[]) >>
      qexistsl_tac [`D`,`Gp`,`d`,`lo`,`pos`,`ss`,`u`,`tp`,`tr`] >>
      fs[Excl "vv_storage_live_def"] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (simp[vv_storage_live_def] >> irule (cj 1 extcall_request_saved_code_endpoint) >>
      simp[] >> qexistsl_tac [`Gp`,`lo`,`pos`,`ss`,`u`,`tp`] >> fs[] >> metis_tac[]) >>
  `p.ptr_location <> LocStorage /\ p.ptr_location <> LocTransient` by
    (fs[slot_loc_def] >> metis_tac[]) >>
  `p.ptr_location = LocCalldata` by (Cases_on `p.ptr_location` >> gvs[]) >>
  fs[vv_holds_def]
QED

Theorem extcall_keyword_packing_rows:
  !mods.
  LENGTH svs = LENGTH xs /\
  local_ptrs_reserved cenv sb /\
  sb.cs_next_var <= se.cs_next_var /\ sb.cs_next_id <= se.cs_next_id /\
  wb_frame cenv pos ee sb u t /\
  ghost_kept_at lo cenv pos sb Gp tp u G tn /\
  (!x w. not_fresh_at sb x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  u.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = u.vs_labels /\
  MAP FDOM ee.scopes = MAP FDOM pos.scopes /\
  expr_sim_inv_mods mods cenv cx env pos /\
  (~exprs_can_mutate cenv kw_es ==> ee.scopes = pos.scopes /\ ee.immutables = pos.immutables /\
     (!tr. get_storage cx ee tr = get_storage cx pos tr)) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H pos.storage_trace /\
    stmt_state_rel H ctx func cenv cx ee t /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
  (!H. valid_horizon cx st0 H pos.storage_trace ==>
    stmt_state_rel H ctx func cenv cx pos u /\
    LIST_REL (\(e,sv) v.
      (?si sm ss vv raw copy.
        compile_expr cenv (expr_type e) e si = (vv,sm) /\
        compile_snapshot_vv cenv copy
          (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
        (~copy ==> ~exprs_can_mutate cenv kw_es) /\
        (copy /\ ~is_word_type (lowered_value_type cenv e) ==>
          ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
            eval_operand (vv_operand sv) u = SOME w /\
            evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
            val_wf tv v /\ FLOOKUP u.vs_allocas sm.cs_next_id =
              SOME (w2n w,type_memory_size tv) /\ sm.cs_next_id < ss.cs_next_id /\
            (!n b len. local_region cenv pos.scopes u n b len ==>
               regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
        sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id /\
        sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
        ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
        local_ptrs_reserved cenv si /\
        (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
        ((?tag op0. sv = StackValue tag op0) \/
         (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
              ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
         (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
              ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
              lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
        read_result cx raw pos = (INL v,pos) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv pos u /\
        vv_at cenv cx (lowered_value_type cenv e) si ss pos raw sv u /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv pos Gp tp u /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) pos raw sv u) /\
      vv_storage_live H cx sv pos u /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op Gp u) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand Gp u) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tp.t_mem u.vs_memory mem ==>
             val_in_memory rt v (w2n w) mem))) (ZIP (xs,svs)) vs) ==>
  !i. i < LENGTH xs ==>
    ?e sv v raw si sm ss vv copy.
      e = EL i xs /\ sv = EL i svs /\ v = EL i vs /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy
        (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      local_ptrs_reserved cenv si /\
      sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
      vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx sv ee t) /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. valid_horizon _ _ H ee.storage_trace` (qx_choose_then `H0` assume_tac) >>
  qx_gen_tac `i` >> disch_tac >>
  (* Project a fixed list position at every valid keyword exit horizon. *)
  qpat_x_assum `!H. valid_horizon _ _ H pos.storage_trace ==> _`
    (mp_tac o SRULE[LIST_REL_EL_EQN]) >>
  simp[] >> disch_then (mk_asm "pos_rows") >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm "pos_rows" (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 kall_tac (qspec_then `i` mp_tac))) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[EL_ZIP, Excl "vv_storage_live_def"] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`old_raw`,`copy`] (MAP_EVERY assume_tac o CONJUNCTS))
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `e = EL i xs` >> qabbrev_tac `sv = EL i svs` >>
  qabbrev_tac `v = EL i vs` >>
  drule_all_then strip_assume_tac keyword_packing_endpoint_frame >>
  drule_all_then strip_assume_tac keyword_packing_restrict_frame >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    metis_tac[extcall_saved_operand_not_fresh] >>
  `ci_mono sm ss` by
    (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_id <= sm.cs_next_id` by
    (drule exprSimUnwrapTheory.compile_expr_extends >> simp[]) >>
  `local_ptrs_reserved cenv ss` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `si` >>
     fs[ci_mono_def] >> decide_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      (?raw. read_result cx raw ee = (INL v,ee) /\
             vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
             vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
             ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
             vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G t)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     `stmt_state_rel H ctx func cenv cx pos u /\ vv_storage_live H cx sv pos u` by
       (asm "pos_rows" (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 kall_tac (qspec_then `i` mp_tac))) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        simp[EL_ZIP, Abbr `sv`, Excl "vv_storage_live_def"]) >>
     irule keyword_packing_row_endpoint >>
     simp[Excl "vv_storage_live_def"] >>
     qexistsl_tac [`DF H`,`Gp`,`copy`,`ctx`,`d`,`env`,`func`,`lo`,`pos`,`sm`,`tp`,`u`,`vv`] >>
     simp[Excl "vv_storage_live_def"] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexists_tac `old_raw` >> simp[]) >>
     disch_tac >>
     qpat_assum `copy /\ ~is_word_type (lowered_value_type cenv e)` (fn premise =>
       qpat_assum `_ ==> ?x w tv. vv_location sv = SOME LocMemory /\ _`
         (qx_choosel_then [`x`,`w`,`tv`] strip_assume_tac o C MATCH_MP premise)) >>
     qexistsl_tac [`x`,`w`,`tv`] >> simp[] >>
     qpat_assum `!n b len. local_region cenv pos.scopes u n b len ==> regions_disjoint _ _ _ _`
       mp_tac >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (?raw. _) /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `raw` strip_assume_tac)
    (CONJUNCTS_THEN2 kall_tac assume_tac)) >>
  qexistsl_tac [`raw`,`si`,`sm`,`ss`,`vv`,`copy`] >>
  simp[Excl "vv_storage_live_def"] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
