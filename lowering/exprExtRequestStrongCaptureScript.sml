(* Compiler-indexed captures keep one fixed historical producer. *)
Theory exprExtRequestStrongCapture
Ancestors
  exprExtRequestCapture exprExtRequestHistory exprExtRequestReconstruct
  exprExtRequestReadProbe loweringPosts exprLowering compileEnv exprSimProps
  list

Definition extrequest_strong_capture_def:
  extrequest_strong_capture ctx func cenv cx e r vv ee sn t <=>
    ?es sa sc s0 ec tc.
      post_value_type cenv e = expr_type e /\
      vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
      local_ptrs_reserved cenv sa /\
      sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
      extrequest_history_frame cenv cx ec sc tc ee sn t /\
      (case vv of StackValue ty op => safe_operand sc op
       | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
      (!ty p tr w tv.
         vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
         eval_operand p.ptr_operand tc = SOME w /\
         evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
         storage_read_live cx tr (get_storage cx ec tr) w tv)
End

Theorem extrequest_strong_capture_intro:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sc s0 ee r vv t /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  local_ptrs_reserved cenv sc /\
  (case vv of StackValue ty op => safe_operand sc op
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p w tv.
     vv = LocatedValue ty p /\ eval_operand p.ptr_operand t = SOME w /\
     evaluate_type (get_tenv cx) ty = SOME tv ==>
     (p.ptr_location = LocStorage ==>
       storage_read_live cx F (get_storage cx ee F) w tv) /\
     (p.ptr_location = LocTransient ==>
       storage_read_live cx T (get_storage cx ee T) w tv)) ==>
  extrequest_strong_capture ctx func cenv cx e r vv ee sc t
Proof
  strip_tac >> simp[extrequest_strong_capture_def] >>
  qexistsl_tac [`es`, `sa`, `sc`, `s0`, `ee`, `t`] >>
  simp[extrequest_history_frame_refl] >> rpt strip_tac >>
  Cases_on `tr` >> gvs[slot_loc_def] >>
  `ty = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  metis_tac[]
QED

Theorem extrequest_strong_capture_projection:
  extrequest_strong_capture ctx func cenv cx e r vv ee sn t /\
  stmt_state_rel ctx func cenv cx ee t ==>
  extrequest_capture ctx func cenv cx e r vv ee t
Proof
  simp[extrequest_strong_capture_def] >> strip_tac >>
  simp[extrequest_capture_def] >>
  qexistsl_tac [`es`, `sa`, `sc`, `s0`, `ec`, `tc`] >> simp[] >>
  conj_tac >- gvs[extrequest_history_frame_def] >>
  conj_tac
  >- (drule_all extrequest_history_holds >> simp[]) >>
  Cases_on `vv` >> gvs[] >> rpt strip_tac >>
  drule_all extrequest_history_operand >> simp[]
QED

Theorem extrequest_strong_capture_extend:
  extrequest_strong_capture ctx func cenv cx captured result value ee sm t /\
  stmt_state_rel ctx func cenv cx ee t /\
  vv_post ctx func cenv cx e ee sm sn t ee' r vv t' /\
  extrequest_read_frame cx ee ee' /\
  local_ptrs_reserved cenv sn /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (!n b sz. local_region cenv ee.scopes t n b sz ==>
     mem_bytes_at b sz t'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!off len.
     (!inst b sz.
        MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,sz) ==>
        compileEnv$regions_disjoint off len b sz) ==>
     mem_bytes_at off len t'.vs_memory = mem_bytes_at off len t.vs_memory) ==>
  extrequest_strong_capture ctx func cenv cx captured result value ee' sn t'
Proof
  simp[extrequest_strong_capture_def] >> strip_tac >>
  qexistsl_tac [`es`, `sa`, `sc`, `s0`, `ec`, `tc`] >> simp[] >>
  irule extrequest_history_frame_extend >>
  qpat_assum `extrequest_history_frame _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `vv_post _ _ _ _ e _ _ _ _ _ _ _ _` (irule_at Any) >>
  gvs[vv_post_def] >> metis_tac[]
QED

Definition extrequest_strong_captures_def:
  extrequest_strong_captures ctx func cenv cx es rs vvs ee sn t <=>
    LENGTH rs = LENGTH vvs /\
    LIST_REL (\e rv. extrequest_strong_capture ctx func cenv cx e
                         (FST rv) (SND rv) ee sn t) es (ZIP (rs,vvs))
End

Theorem extrequest_strong_captures_nil[simp]:
  extrequest_strong_captures ctx func cenv cx [] [] [] ee sn t
Proof
  simp[extrequest_strong_captures_def]
QED

Theorem extrequest_strong_captures_cons[simp]:
  extrequest_strong_captures ctx func cenv cx (e::es) (r::rs) (vv::vvs) ee sn t <=>
  extrequest_strong_capture ctx func cenv cx e r vv ee sn t /\
  extrequest_strong_captures ctx func cenv cx es rs vvs ee sn t
Proof
  simp[extrequest_strong_captures_def] >> metis_tac[]
QED

Theorem extrequest_strong_captures_projection:
  !es rs vvs.
  extrequest_strong_captures ctx func cenv cx es rs vvs ee sn t /\
  stmt_state_rel ctx func cenv cx ee t ==>
  extrequest_captures ctx func cenv cx es rs vvs ee t
Proof
  Induct >> Cases_on `rs` >> Cases_on `vvs` >>
  simp[extrequest_strong_captures_def, extrequest_captures_def] >>
  rpt strip_tac
  >- (irule extrequest_strong_capture_projection >> metis_tac[]) >>
  first_x_assum (drule_all_then mp_tac) >>
  simp[extrequest_strong_captures_def, extrequest_captures_def]
QED

Theorem extrequest_strong_captures_extend:
  !es rs vvs.
  extrequest_strong_captures ctx func cenv cx es rs vvs ee sm t /\
  stmt_state_rel ctx func cenv cx ee t /\
  vv_post ctx func cenv cx e ee sm sn t ee' r vv t' /\
  extrequest_read_frame cx ee ee' /\
  local_ptrs_reserved cenv sn /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  (!n b sz. local_region cenv ee.scopes t n b sz ==>
     mem_bytes_at b sz t'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!off len.
     (!inst b sz.
        MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP t'.vs_allocas inst.inst_id = SOME (b,sz) ==>
        compileEnv$regions_disjoint off len b sz) ==>
     mem_bytes_at off len t'.vs_memory = mem_bytes_at off len t.vs_memory) ==>
  extrequest_strong_captures ctx func cenv cx es rs vvs ee' sn t'
Proof
  Induct >> Cases_on `rs` >> Cases_on `vvs` >>
  simp[extrequest_strong_captures_def] >> rpt strip_tac
  >- (drule_all extrequest_strong_capture_extend >> simp[]) >>
  qpat_x_assum `!rs vvs. _`
    (drule_all_then mp_tac o SRULE [extrequest_strong_captures_def]) >> simp[]
QED
