(* Restrict the memory representation of the reached tuple to one selected cell. *)
Theory bodySubscriptTupleMemoryPostMods
Ancestors
  bodyFullPostsMods bodyPtrAttributeFields exprSimAttributeProps exprSimVVFrame
  exprSimMemDefs exprSimProps exprLoweringProps stateRelProj tupleMemoryLayout
  valueEncodingTyping valueEncodingProofs vyperTypeDefaults vyperPlaceResultTyping
  loweringPosts bodyPtrDefs exprLowering context vyperAST vyperState venomState
  compileEnv valueEncoding valueEncodingDefs vyperInterpreter integer
  finite_map list words arithmetic

Theorem tuple_memory_placement[local]:
  vv_at cenv cx (TupleT tys) sa sb ee raw bvv t /\
  vv_loc bvv = LocMemory /\ eval_operand (vv_operand bvv) t = SOME w /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) ==>
  (?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
               sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
               b <= w2n w /\ w2n w + type_memory_size (TupleTV tvs) <= b + sz /\
               (!n lb lsz. local_region cenv ee.scopes t n lb lsz ==>
                            b + sz <= lb \/ lb + lsz <= b)) \/
  (?n b sz. local_region cenv ee.scopes t n b sz /\
            b <= w2n w /\ w2n w + type_memory_size (TupleTV tvs) <= b + sz /\
            local_path_at cenv cx n (w2n w - b) (TupleTV tvs) /\
            local_place_at cenv cx n (w2n w - b) (TupleTV tvs) raw) \/
  type_memory_size (TupleTV tvs) = 0
Proof
  Cases_on `bvv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, is_word_type_def, local_val_at_def] >>
  rpt strip_tac >> gvs[val_footprint_def, local_place_at_def] >> metis_tac[]
QED

Theorem tuple_memory_selected_at[local]:
  vv_at cenv cx (TupleT tys) sa sb ee raw bvv t /\ vv_loc bvv = LocMemory /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\
  eval_operand (vv_operand bvv) t = SOME w /\ eval_operand dst t = SOME dw /\
  w2n dw = w2n w + off /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\ val_wf ftv fv /\
  off + type_memory_size ftv <= type_memory_size (TupleTV tvs) /\
  mem_step_offset (TupleTV tvs) (ValueSubscript (IntV (&k))) = SOME (off,ftv) /\
  select_result cx (TupleT tys) raw (ValueSubscript (IntV (&k))) ee = (INL raw',ee) ==>
  vv_at cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst LocMemory)) t
Proof
  strip_tac >> drule_all_then strip_assume_tac tuple_memory_placement >>
  drule_then assume_tac select_result_memory_place >>
  simp[vv_at_def, mk_ptr_def] >>
  `val_footprint ftv fv <= type_memory_size ftv` by simp[val_footprint_le] >>
  gvs[]
  >~ [`FLOOKUP t.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_region cenv ee.scopes t n b sz`]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[] >>
      `w2n w - b + off = w2n w + off - b` by decide_tac >>
      `local_place_at cenv cx n (w2n w - b + off) ftv raw'` by
        (irule local_place_at_step >> goal_assum (drule_at Any) >> simp[] >>
         goal_assum (drule_at Any) >> simp[]) >>
      drule_all local_path_at_step >> gvs[local_path_at_val_at] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED

Theorem tuple_memory_base_frontier[local]:
  vv_store_bound cx (TupleT tys) lt ee raw bvv s /\
  vv_loc bvv = LocMemory /\ eval_operand (vv_operand bvv) s = SOME w /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) ==>
  type_memory_size (TupleTV tvs) = 0 \/
  w2n w + type_memory_size (TupleTV tvs) <= s.vs_alloca_next
Proof
  Cases_on `bvv` >>
  simp[vv_store_bound_def, vv_loc_def, vv_location_def, vv_operand_def,
       is_word_type_def, val_store_size_def] >>
  rpt strip_tac >> gvs[type_memory_size_def]
QED

Theorem tuple_memory_base_holds[local]:
  vv_holds_mods cenv cx (TupleT tys) raw bvv ee t /\
  vv_loc bvv = LocMemory /\ eval_operand (vv_operand bvv) t = SOME w /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) ==>
  tuple_in_memory vs tvs (w2n w) t.vs_memory
Proof
  Cases_on `bvv` >>
  simp[vv_holds_mods_def, vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_rel_def, is_word_type_def] >> rpt strip_tac >> gvs[val_in_memory_def]
QED

Theorem tuple_memory_selected_holds[local]:
  val_in_memory ftv fv (w2n dw) t.vs_memory /\ value_has_type ftv fv /\
  read_result cx raw' ee = (INL fv,ee) /\
  eval_operand dst t = SOME dw /\ evaluate_type (get_tenv cx) ann = SOME ftv ==>
  vv_holds_mods cenv cx ann raw' (LocatedValue ann (mk_ptr dst LocMemory)) ee t
Proof
  simp[vv_holds_mods_def, vv_holds_def, mk_ptr_def] >> strip_tac >>
  strip_tac >> drule_all_then ACCEPT_TAC val_in_memory_word_type
QED

Theorem tuple_memory_selected_bound[local]:
  read_result cx raw' ee = (INL fv,ee) /\ eval_operand dst t = SOME dw /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\ val_wf ftv fv /\
  off + type_memory_size ftv <= sz /\ w2n dw = w2n (w:bytes32) + off /\
  (sz <> 0 ==> w2n w + sz <= t.vs_alloca_next) ==>
  vv_store_bound cx ann ann ee raw' (LocatedValue ann (mk_ptr dst LocMemory)) t
Proof
  strip_tac >> drule_then assume_tac val_store_size_le >>
  simp[vv_store_bound_def, mk_ptr_def] >> decide_tac
QED

Theorem tuple_memory_base_ptr[local]:
  ptr_vv_ok cx (TupleT tys) raw bvv ee G tn s /\
  read_result cx raw ee = (INL v,ee) /\ vv_loc bvv = LocMemory ==>
  ptr_mem_ok cx (TupleT tys) v (vv_operand bvv) G tn s
Proof
  Cases_on `bvv` >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, is_word_type_def, vv_operand_def,
       vv_loc_def, vv_location_def] >> rpt strip_tac >> gvs[]
QED

Theorem tuple_memory_selected_buffer[local]:
  ptr_mem_ok cx (TupleT tys) (ArrayV (TupleV vs)) src G tn s /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  eval_operand src s = SOME w /\ eval_operand dst t = SOME dw /\
  off + type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size (TupleTV tvs) /\
  w2n dw = w2n w + off /\
  (!x b sz. src = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
    ?y. dst = Var y /\ FLOOKUP G' y = SOME (b,sz)) ==>
  ptr_buf_ok cenv e dst G' t
Proof
  strip_tac >> simp[ptr_buf_ok_def] >> strip_tac >>
  `type_memory_size (TupleTV tvs) <> 0` by decide_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_mem_ok_def] >>
  disch_then (qspecl_then [`TupleTV tvs`,`w`] mp_tac) >>
  simp[val_footprint_def, val_store_size_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem tuple_memory_selected_robust[local]:
  ptr_mem_ok cx (TupleT tys) (ArrayV (TupleV vs)) src G tn s /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  eval_operand src s = SOME w /\ w2n dw = w2n w + SUM (MAP type_memory_size (TAKE k tvs)) /\
  LENGTH vs = LENGTH tvs /\ k < LENGTH tvs /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem ==>
  !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory (EL k tvs) (EL k vs) (w2n dw) mem
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `mem_agree_outside tn.t_mem s.vs_memory mem` by
    (qpat_x_assum `mem_agree_outside _ _ mem` mp_tac >> asm_rewrite_tac[]) >>
  `tuple_in_memory vs tvs (w2n w) mem` by
    (qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_mem_ok_def] >>
     disch_then (qspecl_then [`TupleTV tvs`,`w`] mp_tac) >>
     simp[val_in_memory_def] >> strip_tac >>
     first_x_assum irule >> fs[]) >>
  qpat_assum `w2n dw = _` SUBST1_TAC >> irule tuple_in_memory_element >> simp[]
QED

Theorem tuple_memory_base_own[local]:
  vv_own cenv cx (TupleT tys) sa sb ee raw bvv t /\ vv_loc bvv = LocMemory ==>
  vv_own cenv cx (TupleT tys) sa sb ee raw
    (LocatedValue (TupleT tys) (mk_ptr (vv_operand bvv) LocMemory)) t
Proof
  Cases_on `bvv` >> simp[vv_own_def, expr_val_own_def, mk_ptr_def,
    vv_operand_def, vv_loc_def, vv_location_def, is_word_type_def] >> metis_tac[]
QED

Theorem tuple_selected_value_base[local]:
  select_result cx ty raw sub ee = (INL (Value v),ee) ==> ?sv. raw = Value sv
Proof
  Cases_on `raw` >> simp[select_result_def, raise_def] >> strip_tac >>
  drule extend_place_result_shape >> simp[]
QED

Theorem tuple_memory_selected_own[local]:
  (!v. raw = Value v ==> vv_own cenv cx (TupleT tys) sa sb ee raw bvv t) /\
  vv_loc bvv = LocMemory /\
  select_result cx (TupleT tys) raw (ValueSubscript (IntV (&k))) ee = (INL raw',ee) /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\ val_wf ftv fv /\
  eval_operand (vv_operand bvv) t = SOME w /\ eval_operand dst t = SOME dw /\
  w2n dw = w2n w + off /\ off + type_memory_size ftv <= type_memory_size (TupleTV tvs) /\
  raw' = Value v ==>
  vv_own cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst LocMemory)) t
Proof
  strip_tac >> gvs[] >> drule_then strip_assume_tac tuple_selected_value_base >>
  first_x_assum (drule_then assume_tac) >>
  drule_all_then assume_tac tuple_memory_base_own >>
  `off + val_footprint ftv fv <= val_footprint (TupleTV tvs) (ArrayV (TupleV vs))` by
    (`val_footprint ftv fv <= type_memory_size ftv` by simp[val_footprint_le] >>
     `val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) = type_memory_size (TupleTV tvs)` by
       simp[val_footprint_def] >>
     decide_tac) >>
  irule vv_own_memory_slice >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`TupleT tys`,`vv_operand bvv`,`Value sv`,`TupleT tys`] >> fs[]
QED

Theorem tuple_subscript_memory_post_mods:
  vv_loc bvv = LocMemory /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  k < LENGTH tvs /\ values_have_types tvs vs /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx raw' ee = (INL (EL k vs),ee) /\
  select_result cx (TupleT tys) raw (ValueSubscript (IntV (&k))) ee = (INL raw',ee) /\
  off = SUM (MAP type_memory_size (TAKE k tvs)) /\
  off + type_memory_size (EL k tvs) <= type_memory_size (TupleTV tvs) /\
  mem_step_offset (TupleTV tvs) (ValueSubscript (IntV (&k))) = SOME (off,EL k tvs) /\
  type_memory_bytes cenv (lowered_value_type cenv (Subscript (EL k tys) obj idx)) =
    type_memory_size (EL k tvs) /\
  vv_holds_mods cenv cx (TupleT tys) raw bvv ee t /\
  vv_at cenv cx (TupleT tys) sa sb ee raw bvv t /\ stmt_state_rel H ctx func cenv cx ee t /\
  vv_store_bound cx (TupleT tys) lt ee raw bvv s /\
  ptr_vv_ok cx (TupleT tys) raw bvv ee G tn s /\
  eval_operand (vv_operand bvv) s = SOME w /\ eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w off) /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\ op_taint tn' dst = {} /\
  (!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
    ?y. dst = Var y /\ FLOOKUP G' y = SOME (b,sz)) /\
  (!v. raw = Value v ==> vv_own cenv cx (TupleT tys) sa sb ee raw bvv t) ==>
  let ann = EL k tys; vv = LocatedValue ann (mk_ptr dst LocMemory) in
    vv_holds_mods cenv cx ann raw' vv ee t /\
    vv_at cenv cx ann sa sb ee raw' vv t /\
    vv_store_bound cx ann ann ee raw' vv t /\
    ptr_vv_ok cx ann raw' vv ee G' tn' t /\
    ptr_buf_ok cenv (Subscript ann obj idx) dst G' t /\
    (!v. raw' = Value v /\ ~is_word_type ann /\ ~is_bytestring_type ann ==>
      vv_own cenv cx ann sa sb ee raw' vv t)
Proof
  strip_tac >> simp[LET_THM] >>
  `LENGTH vs = LENGTH tvs /\ value_has_type (EL k tvs) (EL k vs)` by
    fs[values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  `val_wf (EL k tvs) (EL k vs)` by
    drule_then ACCEPT_TAC (cj 1 value_has_type_val_wf) >>
  `type_memory_size (TupleTV tvs) <> 0 ==>
   w2n w + type_memory_size (TupleTV tvs) <= t.vs_alloca_next` by
    (drule_all tuple_memory_base_frontier >> simp[] >> decide_tac) >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac alloca_room_next_lt >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule field_ptr_w2n >> qexistsl_tac [`type_memory_size (EL k tvs)`,`type_memory_size (TupleTV tvs)`] >>
     simp[] >> decide_tac) >>
  `ptr_buf_ok cenv (Subscript (EL k tys) obj idx) dst G' t` by
    (drule_all_then assume_tac tuple_memory_base_ptr >>
     irule tuple_memory_selected_buffer >>
     goal_assum (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`w + n2w off`,`off`,`tvs`,`w`] >> simp[]) >>
  (conj_tac >- suspend "holds") >>
  (conj_tac >- (drule_all tuple_memory_selected_at >> simp[])) >>
  (conj_tac >- (irule tuple_memory_selected_bound >>
    goal_assum (drule_at (Pat `read_result _ _ _ = _`)) >>
    qexistsl_tac [`w + n2w off`,`EL k tvs`,`off`,`type_memory_size (TupleTV tvs)`,`w`] >> simp[])) >>
  (conj_tac >- suspend "safe") >>
  simp[] >> rpt strip_tac >> drule_all tuple_memory_selected_own >> simp[]
QED

Resume tuple_subscript_memory_post_mods[holds]:
  irule tuple_memory_selected_holds >> goal_assum (drule_at (Pat `read_result _ _ _ = _`)) >>
  simp[IgnAsm `off = _`, IgnAsm `t.vs_memory = _`] >>
  drule_all_then assume_tac tuple_memory_base_holds >>
  rewrite_tac[Once ADD_COMM] >>
  qpat_assum `off = _` SUBST1_TAC >> irule tuple_in_memory_element >> simp[]
QED

Resume tuple_subscript_memory_post_mods[safe]:
  drule_all_then assume_tac tuple_memory_base_ptr >>
  irule ptr_vv_ok_memory >> simp[mk_ptr_def] >>
  irule ptr_mem_ok_of_buffer >> goal_assum (drule_at (Pat `ptr_buf_ok _ _ _ _ _`)) >>
  simp[IgnAsm `off = _`, IgnAsm `t.vs_memory = _`, IgnAsm `tn'.t_mem = _`] >>
  gen_tac >> strip_tac >>
  `w2n (w + n2w off) = w2n w + SUM (MAP type_memory_size (TAKE k tvs))` by
    (qpat_assum `w2n (w + n2w off) = _` SUBST1_TAC >> simp[]) >>
  drule_all tuple_memory_selected_robust >> simp[]
QED

Finalise tuple_subscript_memory_post_mods
