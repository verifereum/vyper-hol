Theory createCtorTupleUnwrap
Ancestors
  exprSimUnwrap exprSimProps loweringPosts vyperAST vyperInterpreter
  exprLoweringProps fragGasMode fragGasPath exprSimMemoryPath
  exprSimUnwrapProps vyperState venomState

(* A captured result is not re-evaluated.  Pop is only an adapter for the
   effectful postcondition, so neither liveness nor a pure frame is needed. *)
Theorem ctor_captured_vv_post:
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin sm es raw vv s ==>
  vv_post H ctx func ce cx (Pop ty (NameTarget ""))
    es origin sm s es raw vv s
Proof
  simp[vv_post_def, expr_type_def]
QED

Theorem ctor_captured_unwrap_post_path:
  unwrap_value ce vv sm = (op,sn) /\
  local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sm.cs_next_var /\
  origin.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt /\ ~is_word_type ty ==>
     type_memory_bytes ce ty = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin sm es raw vv s /\
  read_result cx raw es = (INL v,es) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post H ctx func ce cx (Pop ty (NameTarget ""))
      es origin sn s es v op u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  drule_all ctor_captured_vv_post >> strip_tac >>
  drule_all exprSimUnwrapPropsTheory.vv_post_read_result >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_path_fields >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[expr_type_def, gas_marked_path_def]
QED

(* The provenance cutoff is origin; the frame cutoff is sm.  In particular
   this protects a tuple allocated between capture and delayed unwrapping. *)
Theorem ctor_captured_unwrap_frame[local]:
  unwrap_value ce vv sm = (op,sn) /\
  local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sm.cs_next_var /\
  origin.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt /\ ~is_word_type ty ==>
     type_memory_bytes ce ty = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin sm es raw vv s /\
  read_result cx raw es = (INL v,es) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post H ctx func ce cx (Pop ty (NameTarget ""))
      es origin sn s es v op u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       aid < sm.cs_next_id /\
       (!n b k. local_region ce es.scopes s n b k ==>
          off + sz <= b \/ b + k <= off) ==>
       mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory)
Proof
  strip_tac >>
  `local_ptrs_reserved ce sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  drule_all ctor_captured_vv_post >> strip_tac >>
  drule_all exprSimUnwrapPropsTheory.vv_post_read_result >> strip_tac >>
  Cases_on `vv`
  >- (gvs[exprLoweringTheory.unwrap_value_def, compileEnvTheory.comp_return_def] >>
      qexists_tac `s` >> simp[gas_marked_path_def, cj 1 gas_path_rules] >>
      irule expr_post_of_vv_post_stack >> goal_assum (drule_at Any)) >>
  rename1 `LocatedValue t p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >>
  `vv_at ce cx ty sm sm es raw (LocatedValue t p) s` by
    gvs[vv_at_def] >>
  `?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post H ctx func ce cx (Pop ty (NameTarget ""))
      es sm sn s es v op u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx` by
    (irule ctor_captured_unwrap_post_path >>
     simp[] >> qexistsl_tac [`raw`, `sm`, `LocatedValue t p`] >> simp[]) >>
  qexists_tac `u` >> gvs[expr_post_def, expr_type_def] >>
  rpt conj_tac >> rpt strip_tac >>
  metis_tac[expr_val_at_start_mono, freshWritesTheory.not_fresh_at_mono,
            arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Resume ctor_captured_unwrap_frame[memory]:
  Cases_on `is_word_type t`
  >- ( `t = ty /\ ?w. eval_operand p.ptr_operand s = SOME w /\
         (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt ==>
           mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v)` by
         gvs[vv_post_def, vv_holds_def, valueCopyBytesTheory.is_bytestring_word_type,
             read_result_def, vyperStateTheory.return_def, expr_type_def] >>
       gvs[unwrap_memory_compile] >>
       qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var))
         (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
       `eval_operand op u = SOME (mload (w2n w) s) /\
        u.vs_current_bb = sn.cs_current_bb /\
        u.vs_inst_idx = LENGTH sn.cs_current_insts /\
        (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
          lookup_var x u = SOME w') /\
        u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
         (qunabbrev_tac `u` >> irule emit_mload_endpoint >>
          simp[] >> qexists_tac `p.ptr_operand` >> simp[]) >>
       `gas_marked_path F ctx func s 0 (OK u)` by
         (drule_all emit_mload_marked_path >> simp[Abbr `u`]) >>
       `u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
        u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx` by
         simp[Abbr `u`, update_var_def] >>
       qexists_tac `u` >> simp[] >>
       irule expr_post_of_vv_post_load_physical >> simp[expr_type_def] >>
       conj_tac
       >- (rpt strip_tac >> fs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
       conj_tac
       >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
           irule stmt_state_rel_update_var >> simp[] >>
           irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
       qexistsl_tac [`p`, `s`, `sm`, `t`] >> simp[]) >>
  gvs[unwrap_memory_compile, compileEnvTheory.comp_return_def] >>
  qexists_tac `s` >> simp[gas_marked_path_def, cj 1 gas_path_rules] >>
  irule expr_post_of_vv_post_memory >> simp[] >> qexists_tac `t` >> simp[]
QED

Finalise ctor_captured_unwrap_frame

(* Public delayed-read boundary: representation retains its capture provenance,
   while the exterior frame is relative to the later unwrap cursor. *)
Theorem ctor_captured_unwrap_path:
  unwrap_value ce vv sm = (op,sn) /\
  local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sm.cs_next_var /\
  origin.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!tvt. evaluate_type (get_tenv cx) ty = SOME tvt /\ ~is_word_type ty ==>
     type_memory_bytes ce ty = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64) /\
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin sm es raw vv s /\
  read_result cx raw es = (INL v,es) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ expr_val_at ce cx ty origin sn es v op u /\
    stmt_state_rel H ctx func ce cx es u /\
    storage_well_formed_on cx es (FST H) /\
    alloca_inv u /\ alloca_room ctx func u /\ fmp_room ctx func u /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b) /\
    locals_kept ce es es s u /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
       aid < sm.cs_next_id /\
       (!n b k. local_region ce es.scopes s n b k ==>
          off + sz <= b \/ b + k <= off) ==>
       mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory)
Proof
  strip_tac >> drule_all ctor_captured_unwrap_frame >> strip_tac >>
  `~u.vs_halted` by
    (fs[gas_marked_path_def] >> drule gas_path_normal >> simp[]) >>
  qexists_tac `u` >> gvs[expr_post_def, expr_type_def] >>
  gvs[stmt_state_rel_def] >> metis_tac[]
QED
