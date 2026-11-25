(* Transport the child resources through the destination ALLOCA, then
   unwrap on the same joint endpoint used by the default store. *)
Theory bodyFullExtCallDefaultUnwrap
Ancestors
  bodyFullUnwrap bodyPtrIfExpAllocSource revertReasonPrefixPtr
  robustCopyTransportPtr stateRelProj
  valueTypingMemoryProps bodyFullHashKeccakFixed fragGasOriginPtrExec
  assignBasePtrBoundary wordArgsPtr finite_map words
  bodyPtrDefs ptrDiscipline loweringPosts context venomState
  exprSimMemDefs exprLoweringProps vyperStorageFootprint logValueFramePtr
  exprOperandVar valueCopyBytes fragGasPathFrameMem fragGasSeqPtr
  decoderGhostFramePtr venomMemDefs allocaHistory
Libs ctorCopyObservationLib

Theorem default_alloc_robust_frame[local]:
  val_wf tv v /\ u.vs_memory = s.vs_memory /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  (!i. p <= i /\ i < p + val_footprint tv v ==> i < s.vs_alloca_next) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside ta.t_mem u.vs_memory m ==> val_in_memory tv v p m
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule robust_val_in_memory_decreasing_taint_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`s.vs_memory`, `u.vs_memory`, `val_footprint tv v`,
                `p`, `tn.t_mem`, `ta.t_mem`] >>
  simp[] >> rpt strip_tac >>
  `i + p < s.vs_alloca_next` by (first_x_assum irule >> decide_tac) >>
  qpat_x_assum `!i. i < _ ==> (i IN _ <=> _)`
    (qspec_then `i + p` mp_tac) >> simp[]
QED

Theorem default_alloc_ptr_mem_frame[local]:
  ptr_mem_ok cx ty v op G tn s /\
  eval_operand op u = eval_operand op s /\ op_prov Ga op = op_prov G op /\
  u.vs_memory = s.vs_memory /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  (!tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand op s = SOME w ==> val_wf tv v /\
     !i. w2n w <= i /\ i < w2n w + val_footprint tv v ==> i < s.vs_alloca_next) ==>
  ptr_mem_ok cx ty v op Ga ta u
Proof
  strip_tac >> simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `eval_operand op s = SOME w` by metis_tac[] >>
  qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
  disch_then (qspecl_then [`tv`, `w`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  conj_tac
  >- (match_mp_tac (REWRITE_RULE [AND_IMP_INTRO] default_alloc_robust_frame) >>
      simp[] >> metis_tac[]) >>
  strip_tac >>
  `?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
      b <= w2n w /\ w2n w + val_store_size tv v <= b + sz` by metis_tac[] >>
  gvs[op_prov_def] >> metis_tac[]
QED

Theorem default_alloc_ptr_vv_frame[local]:
  ptr_vv_ok cx ty raw vv ee G tn s /\
  stmt_state_rel H ctx func cenv cx ee s /\ vv_at cenv cx ty sa sm ee raw vv s /\
  ~is_word_type ty /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
  op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv) /\
  u.vs_memory = s.vs_memory /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) ==>
  ptr_vv_ok cx ty raw vv ee Ga ta u
Proof
  strip_tac >> Cases_on `vv`
  >- (rename1 `StackValue tag op` >>
      gvs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def] >>
      irule default_alloc_ptr_mem_frame >> simp[] >>
      qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> rpt strip_tac >>
      drule_all (SIMP_RULE (srw_ss()) [vv_operand_def]
        (Q.INST [`vv` |-> `StackValue tag op`] (SPEC_ALL vv_at_memory_footprint))) >> simp[]) >>
  rename1 `LocatedValue tag p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (gvs[vv_operand_def, ptr_vv_ok_def] >>
      irule default_alloc_ptr_mem_frame >> simp[] >>
      qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> rpt strip_tac >>
      metis_tac[located_vv_at_memory_footprint]) >>
  gvs[vv_operand_def] >>
  irule ptr_vv_ok_nonmemory_frame >>
  (metis_tac[])
QED

(* ALLOCA may reuse a site. The frame needed for the child is agreement
   below its old allocation frontier, not freshness of the destination. *)
val default_unwrap_entry = ``
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sn = (op,sc) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id < sn.cs_next_id /\
  fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size ptv /\
  type_memory_size ptv < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
  (post_value_type cenv e = lowered_value_type cenv e \/
   is_bytestring_type (post_value_type cenv e) /\
   is_bytestring_type (lowered_value_type cenv e)) /\
  (!v. read_result cx tv ee = (INL v,ee) ==>
       value_has_type ptv v /\ value_has_type ltv v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  vv_post (storage_trace_horizon ee.storage_trace)
    ctx func cenv cx e es sa sm s0 ee tv vv s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv u /\
      ghost_inv_at (DF H) lo d cenv cx ee Ga ta u) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 Ga ta /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func u /\ lo <= s.vs_alloca_next /\
  s.vs_alloca_next <= u.vs_alloca_next /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  u with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx |> = s /\
  (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  not_fresh_at sn q /\ lookup_var q u = SOME dw /\ ptr_covers Ga ta q u n /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n dw,n) /\
  FLOOKUP Ga q = SOME (w2n dw,n) /\ w2n dw + n <= u.vs_alloca_next /\
  (!name b len. local_region cenv ee.scopes u name b len ==>
      regions_disjoint (w2n dw) n b len) ==>
  ?v z G' tn' sw.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Ga,ta) [] (OK z,G',tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    ghost_kept_at lo cenv ee sn Ga ta u G' tn' /\
    wb_frame cenv ee ee sn u z /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x u /\
         FLOOKUP G' x = FLOOKUP Ga x /\ op_taint tn' (Var x) = op_taint ta (Var x)) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    u.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = u.vs_labels /\ ~z.vs_halted /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    not_fresh_at sc q /\ lookup_var q z = SOME dw /\ ptr_covers G' tn' q z n /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,n) /\
    FLOOKUP G' q = SOME (w2n dw,n) /\ w2n dw + n <= z.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
       regions_disjoint (w2n dw) n b len) /\
    eval_operand op z = SOME sw /\
    (!x. op = Var x ==> not_fresh_at sc x) /\
    ptr_mem_ok cx (post_value_type cenv e) v op G' tn' z /\
    value_has_type ltv v /\ val_wf ltv v /\
    (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
         val_in_memory ltv v (w2n sw) mem) /\
    (type_memory_size ltv <> 0 ==>
       (?x. op = Var x /\ ptr_covers G' tn' x z (type_memory_size ltv)) /\
       w2n sw + type_memory_size ltv <= z.vs_alloca_next) /\
    (val_footprint ptv v = 0 \/
     regions_disjoint (w2n dw) n (w2n sw) (val_footprint ptv v))``;

val unwrap_observer_law =
  ctorCopyObservationLib.close_except
    ["R","ctx","func","cenv","e","sa","sm","sn","sc","vv","op","explicit","PG"]
    (ctorCopyObservationLib.rename "sb" "sn"
      (ctorCopyObservationLib.observe "s" "z" NONE (concl unwrap_value_origin_ptr)));
val (default_unwrap_pre,default_unwrap_post_observed) = dest_imp
  (ctorCopyObservationLib.observe "u" "z" NONE default_unwrap_entry);

Theorem extcall_default_unwrap_store_entry_observed:
  ^default_unwrap_pre ==> ^unwrap_observer_law ==> ^default_unwrap_post_observed
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s /\
   vv_at cenv cx (post_value_type cenv e) sa sm ee tv vv s` by fs[vv_post_def] >>
  `u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_memory = s.vs_memory /\
   u.vs_labels = s.vs_labels` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                          vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
   op_prov Ga (vv_operand vv) = op_prov G (vv_operand vv) /\
   op_taint ta (vv_operand vv) = op_taint tn (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def,op_prov_def,op_taint_def] >>
     metis_tac[]) >>
  `ptr_vv_ok cx (post_value_type cenv e) tv vv ee Ga ta u` by
    metis_tac[default_alloc_ptr_vv_frame] >>
  `vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv u` by
    metis_tac[vv_store_bound_frame_mem_src] >>
  `!x. vv_operand vv = Var x ==> FLOOKUP Ga x = FLOOKUP G x` by metis_tac[] >>
  `!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
      ptr_buf_ok cenv e op0 Ga u` by
    (rpt strip_tac >> irule ptr_buf_ok_frame >> qexistsl [`G`,`s`] >>
     gvs[vv_operand_def]) >>
  `!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand Ga u` by
    (rpt strip_tac >> irule ptr_buf_ok_frame >> qexistsl [`G`,`s`] >>
     gvs[vv_operand_def]) >>
  `cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside ta.t_mem u.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)` by
    (strip_tac >> qpat_assum `cenv.ce_is_ctor /\ _ ==> _` drule_all >>
     disch_then (qx_choose_then `val` strip_assume_tac) >>
     qexists `val` >> conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     `eval_operand (vv_operand vv) s = SOME w` by metis_tac[] >>
     `w2n w + type_memory_size rt <= lo` by metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `rt = ptv` by metis_tac[optionTheory.SOME_11] >>
     `val_wf rt val` by metis_tac[value_has_type_memory_wf] >>
     `val_footprint rt val <= type_memory_size rt` by metis_tac[exprSimPropsTheory.val_footprint_le] >>
     `!i. w2n w <= i /\ i < w2n w + val_footprint rt val ==> i < s.vs_alloca_next` by
       (rpt strip_tac >> decide_tac) >>
     `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rt val (w2n w) mem` by
       (qpat_assum `!rt w. evaluate_type _ _ = _ /\ eval_operand _ s = _ ==> _`
          (qspecl_then [`rt`,`w`] mp_tac) >> simp[]) >>
     match_mp_tac default_alloc_robust_frame >>
     simp[]) >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64` by (simp[] >> (gvs[])) >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type ptv v` by metis_tac[] >>
  `sm.cs_next_id <= sn.cs_next_id` by decide_tac >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`] strip_assume_tac) >>
  suspend "store_entry"
QED

Resume extcall_default_unwrap_store_entry_observed[store_entry]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (strip_assume_tac o UNDISCH)) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
  drule fragGasPathPtrTheory.gas_path_ptr_erase >> strip_tac >>
  `~z.vs_halted /\ z.vs_labels = u.vs_labels` by
    metis_tac[gas_path_ptr_ok_not_halted, gas_path_code_labels] >>
  drule exprSimWordArgsTheory.expr_post_state >> strip_tac >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  `z.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `lookup_var q z = SOME dw /\ FLOOKUP G' q = SOME (w2n dw,n) /\
   op_taint tn' (Var q) = op_taint ta (Var q)` by
    (qpat_assum `!x. not_fresh_at sn x ==> lookup_var x z = _ /\ _`
       (qspec_then `q` mp_tac) >> simp[]) >>
  `ptr_covers G' tn' q z n` by
    (qpat_assum `ptr_covers Ga ta q u n`
       (mp_then (Pos hd) mp_tac ptr_covers_frame) >> simp[]) >>
  `FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,n)` by
    (qpat_assum `wb_frame cenv ee ee sn u z` (mp_tac o REWRITE_RULE [wb_frame_def]) >>
     metis_tac[]) >>
  `w2n dw + n <= z.vs_alloca_next` by decide_tac >>
  `not_fresh_at sc q` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sn` >> simp[] >>
     mp_tac (Q.SPECL [`cenv`,`vv`,`sn`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(case vv of StackValue tag operand => !x. operand = Var x ==> not_fresh_at sn x
               | LocatedValue tag p => !x. p.ptr_operand = Var x ==> not_fresh_at sn x)` by
    (Cases_on `vv` >> fs[vv_operand_def]) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (drule compiler_unwrap_value_var >> simp[]) >>
  `local_ptrs_reserved cenv sn` by suspend "locals_reserved" >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
       regions_disjoint (w2n dw) n b len` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  `?sw. eval_operand op z = SOME sw` by fs[expr_post_def,expr_val_rel_def] >>
  `ptr_mem_ok cx (post_value_type cenv e) v op G' tn' z /\
   op_taint tn' op = {}` by fs[ptr_val_ok_def] >>
  `value_has_type ltv v` by metis_tac[] >>
  `val_wf ltv v` by metis_tac[value_has_type_memory_wf] >>
  `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
       val_in_memory ptv v (w2n sw) mem` by
    (qpat_assum `ptr_mem_ok _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     disch_then (qspecl_then [`ptv`,`sw`] mp_tac) >> simp[]) >>
  qexistsl [`v`,`z`,`G'`,`tn'`,`sw`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "layout" >>
  conj_tac >- suspend "capacity" >>
  suspend "separation"
QED

Resume extcall_default_unwrap_store_entry_observed[locals_reserved]:
  metis_tac[local_ptrs_reserved_next_var]
QED

Resume extcall_default_unwrap_store_entry_observed[layout]:
  rpt strip_tac >>
  qpat_x_assum `post_value_type cenv e = lowered_value_type cenv e \/ _`
    strip_assume_tac
  >- (fs[] >> metis_tac[optionTheory.SOME_11]) >>
  irule bytestring_val_in_memory_transfer >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`post_value_type cenv e`,`lowered_value_type cenv e`,`get_tenv cx`,`ptv`] >>
  simp[]
QED

Resume extcall_default_unwrap_store_entry_observed[capacity]:
  strip_tac >> conj_tac
  >- (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >> simp[] >>
      qexistsl [`cenv`,`e`] >> simp[]) >>
  qpat_assum `~is_word_type _ ==> !rt w. _`
    (mp_tac o Q.SPECL [`ltv`,`sw`] o UNDISCH) >>
  (impl_tac >- simp[]) >> strip_tac >>
  fs[] >> decide_tac
QED

Resume extcall_default_unwrap_store_entry_observed[separation]:
  (* A zero-footprint result need not supply an owning region. *)
  Cases_on `val_footprint ptv v = 0` >- simp[] >> disj2_tac >>
  `alloca_inv z` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `!aid b sz. aid <> sm.cs_next_id /\ FLOOKUP z.vs_allocas aid = SOME (b,sz) ==>
       w2n dw + n <= b \/ b + sz <= w2n dw` by
    (qpat_assum `alloca_inv z`
       (mp_tac o REWRITE_RULE [alloca_inv_def,allocas_non_overlapping_def]) >>
     strip_tac >> rpt strip_tac >> metis_tac[]) >>
  pop_assum (mk_asm "other_alloca") >>
  `?a b. vv_at cenv cx (post_value_type cenv e) a b ee tv
            (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
          (b.cs_next_id <= sm.cs_next_id \/ sm.cs_next_id < a.cs_next_id)` by
    (qpat_assum `~is_word_type _ ==> _ \/ _` (strip_assume_tac o UNDISCH)
     >- (qexistsl [`sa`,`sm`] >> simp[]) >>
     qexistsl [`sn`,`sc`] >> simp[]) >>
  qpat_assum `vv_at _ _ _ _ _ _ _ (LocatedValue _ _) z`
    (mp_tac o REWRITE_RULE [CONJUNCT2 vv_at_def,mk_ptr_def]) >> simp[] >>
  (strip_tac
   >- (rename1 `FLOOKUP z.vs_allocas src_site = SOME (src_base,src_size)` >>
       `src_site <> sm.cs_next_id` by decide_tac >>
       asm "other_alloca" (qspecl_then [`src_site`,`src_base`,`src_size`] mp_tac) >>
       simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
       strip_tac >> decide_tac) >>
   rename1 `local_region cenv ee.scopes z src_name src_base src_size` >>
   qpat_assum `!name b len. local_region cenv ee.scopes z name b len ==>
       regions_disjoint (w2n dw) n b len`
     (qspecl_then [`src_name`,`src_base`,`src_size`] mp_tac) >>
   simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
   strip_tac >> decide_tac)
QED

Finalise extcall_default_unwrap_store_entry_observed

Theorem extcall_default_unwrap_store_entry:
  ^default_unwrap_entry
Proof
  disch_then (mp_tac o MATCH_MP
    (Q.INST [`R` |-> `\p q. T`] extcall_default_unwrap_store_entry_observed)) >>
  BETA_TAC >> REWRITE_TAC [] >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC unwrap_value_origin_ptr)) >>
  disch_then ACCEPT_TAC
QED
