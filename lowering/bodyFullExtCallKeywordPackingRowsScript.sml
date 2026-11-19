(* Saved positional operands at the physical exit of successful keywords. *)
Theory bodyFullExtCallKeywordPackingRows
Ancestors
  bodyFullExtCallPosTransport bodyFullExtCallSavedOperand
  exprSimProps stateRelProj freshWrites loweringPosts bodyPtrDefs
  exprLoweringProps context vyperStorageFootprint vyperStorageBackend vyperState list

(* The positional snapshot owns only IDs and variables already old at the
   keyword entry. Restrict the frame, not the value's compiler interval. *)
Theorem keyword_packing_restrict_frame[local]:
  ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id /\
  pure_frame cenv func pos sb u t /\
  ghost_kept_at lo cenv pos sb Gp tp u G tn /\
  (!x w. not_fresh_at sb x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) ==>
  pure_frame cenv func pos ss u t /\
  ghost_kept_at lo cenv pos ss Gp tp u G tn /\
  (!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w)
Proof
  strip_tac >>
  `!x. not_fresh_at ss x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  rpt conj_tac
  >- (fs[pure_frame_def] >> rpt conj_tac
      >- metis_tac[] >>
      rpt strip_tac >>
      qpat_assum `!off len. _ ==> mem_bytes_at off len _ = _` irule >>
      rpt strip_tac >> first_x_assum irule >>
      qexists_tac `inst` >> simp[] >> decide_tac)
  >- (fs[ghost_kept_at_def] >> conj_tac
      >- (rpt strip_tac >> rename1 `aid < ss.cs_next_id` >>
          `aid < sb.cs_next_id` by decide_tac >>
          rename1 `FLOOKUP u.vs_allocas aid = SOME (off,sz)` >>
          rename1 `i IN tp.t_mem` >>
          qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
            (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >> metis_tac[]) >>
      first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem keyword_packing_endpoint_frame[local]:
  stmt_state_rel H ctx func cenv cx pos u /\
  stmt_state_rel H ctx func cenv cx ee t /\
  local_ptrs_reserved cenv sb /\
  (!x w. not_fresh_at sb x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) /\
  (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
  (pos with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) ==>
  alloca_inv t /\ ee.immutables = pos.immutables /\
  (!tr. get_storage cx ee tr = get_storage cx pos tr) /\
  (!n b sz. local_region cenv pos.scopes u n b sz <=>
             local_region cenv ee.scopes t n b sz)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv pos.scopes u /\ alloca_inv t` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `ee.scopes = pos.scopes /\ ee.immutables = pos.immutables /\
   (!tr. get_storage cx ee tr = get_storage cx pos tr)` by
    (qpat_assum `(ee with <|gas_obs := []; outcomes := NONE; requests := [];
                             storage_trace := []|>) = _` mp_tac >>
     simp[vyperStateTheory.evaluation_state_component_equality] >>
     rpt strip_tac >> Cases_on `tr` >> simp[get_storage_def]) >>
  simp[] >> rpt gen_tac >> eq_tac >> strip_tac
  >- (irule local_region_frame_fwd >> qexistsl_tac [`u`,`sb`,`pos.scopes`] >> simp[]) >>
  irule local_region_frame >> conj_tac >- (qexists_tac `func` >> simp[]) >>
  qexistsl_tac [`sb`,`ee.scopes`,`t`] >> simp[]
QED

(* This is a one-horizon row. The selected witness serves the dynamic
   conjuncts; storage liveness can subsequently be projected at any horizon. *)
Theorem keyword_packing_row_endpoint[local]:
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
         vv_store_bound cx (expr_type e) (lowered_value_type cenv e) pos raw sv u) /\
  vv_storage_live H cx sv pos u /\
  (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
    ptr_buf_ok cenv e op Gp u) /\
  (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand Gp u) /\
  (!x. vv_operand sv = Var x ==> not_fresh_at ss x) /\
  pure_frame cenv func pos ss u t /\
  ghost_kept_at lo cenv pos ss Gp tp u G tn /\
  (!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  u.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = u.vs_labels /\
  alloca_inv t /\ ee.immutables = pos.immutables /\
  (!tr. get_storage cx ee tr = get_storage cx pos tr) /\
  (!n b sz. local_region cenv pos.scopes u n b sz <=>
             local_region cenv ee.scopes t n b sz) /\
  stmt_state_rel H ctx func cenv cx ee t /\
  ghost_inv_at D lo d cenv cx ee G tn t /\ dead_lo_ok H D lo cenv cx ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
         vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
         vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
         ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
         vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
  vv_storage_live H cx sv ee t /\
  ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
    | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok cenv e (vv_operand sv) G t)
Proof
  namedCases_on `sv` ["tag op", "tag p"] >>
  simp[vv_operand_def, Excl "vv_storage_live_def"] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (simp[vv_storage_live_def] >> irule extcall_request_saved_stack_endpoint >>
      simp[ci_mono_refl] >> qexistsl_tac [`Gp`,`func`,`lo`,`pos`,`ss`,`u`,`tp`] >>
      simp[ci_mono_refl]) >>
  `tag = lowered_value_type cenv e /\ ~is_word_type (lowered_value_type cenv e)` by
    (qpat_assum `_ \/ _` mp_tac >> metis_tac[]) >>
  qpat_x_assum `tag = lowered_value_type cenv e` SUBST_ALL_TAC >>
  qpat_x_assum `_ \/ _` kall_tac >>
  Cases_on `p.ptr_location = LocMemory`
  >- (simp[vv_storage_live_def] >> irule extcall_request_saved_memory_endpoint >>
      simp[ci_mono_refl] >> qexistsl_tac [`Gp`,`func`,`lo`,`pos`,`ss`,`u`,`tp`] >>
      simp[ci_mono_refl]) >>
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
  LENGTH svs = LENGTH xs /\
  local_ptrs_reserved cenv sb /\
  sb.cs_next_var <= se.cs_next_var /\ sb.cs_next_id <= se.cs_next_id /\
  pure_frame cenv func pos sb u t /\
  ghost_kept_at lo cenv pos sb Gp tp u G tn /\
  (!x w. not_fresh_at sb x /\ lookup_var x u = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  u.vs_alloca_next <= t.vs_alloca_next /\ t.vs_labels = u.vs_labels /\
  (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
  (pos with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    valid_horizon cx st0 H pos.storage_trace /\
    stmt_state_rel H ctx func cenv cx ee t /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t) /\
  (!H. valid_horizon cx st0 H pos.storage_trace ==>
    stmt_state_rel H ctx func cenv cx pos u /\
    LIST_REL (\(e,sv) v.
      (?si sm ss vv raw.
        compile_expr cenv (expr_type e) e si = (vv,sm) /\
        compile_snapshot_vv cenv F
          (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
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
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) pos raw sv u) /\
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
    ?e sv v raw si sm ss vv.
      e = EL i xs /\ sv = EL i svs /\ v = EL i vs /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv F
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
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t /\
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
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`old_raw`] (MAP_EVERY assume_tac o CONJUNCTS))
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `e = EL i xs` >> qabbrev_tac `sv = EL i svs` >>
  qabbrev_tac `v = EL i vs` >>
  drule_all_then strip_assume_tac keyword_packing_endpoint_frame >>
  drule_all_then strip_assume_tac keyword_packing_restrict_frame >>
  `!x. vv_operand sv = Var x ==> not_fresh_at ss x` by
    metis_tac[extcall_saved_operand_not_fresh] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      (?raw. read_result cx raw ee = (INL v,ee) /\
             vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
             vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
             ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
             vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G t)` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     `vv_storage_live H cx sv pos u` by
       (asm "pos_rows" (qspec_then `H` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (CONJUNCTS_THEN2 kall_tac
          (CONJUNCTS_THEN2 kall_tac (qspec_then `i` mp_tac))) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        simp[EL_ZIP, Abbr `sv`, Excl "vv_storage_live_def"]) >>
     irule keyword_packing_row_endpoint >>
     simp[Excl "vv_storage_live_def"] >> conj_tac
     >- (qexists_tac `vv` >> first_assum ACCEPT_TAC) >>
     qpat_assum `ghost_kept_at _ _ _ ss _ _ _ _ _` (irule_at Any) >>
     qpat_assum `stmt_state_rel H _ _ _ _ ee t` (irule_at Any) >>
     qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[Excl "vv_storage_live_def"] >> qexists_tac `old_raw` >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (?raw. _) /\ _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `raw` strip_assume_tac)
    (CONJUNCTS_THEN2 kall_tac assume_tac)) >>
  qexistsl_tac [`raw`,`si`,`sm`,`ss`,`vv`] >>
  simp[Excl "vv_storage_live_def"] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
