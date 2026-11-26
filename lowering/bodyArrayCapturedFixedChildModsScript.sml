(* Physical child of a captured fixed array at an already reached endpoint. *)
Theory bodyArrayCapturedFixedChildMods
Ancestors
  bodyFullSubscriptCapturedPlace bodyFullTargetArrayLoad exprSimVVFrame
  exprSimSubscriptArrayFramed bodyPtrBopHashFootprint bodyPtrBopHashFrame
  exprSimMemDefs exprSimProps exprLowering[qualified,ignore_grammar]
  abiDecodeStaticProps vyperLookupStorage valueEncodingProps bodyPtrDefs ptrDiscipline
  loweringStateRelDefs loweringPosts context venomState words

Theorem captured_child_readonly[local]:
  array_length_frame st2 it Gi tni q Gq tq ==>
  q.vs_memory = it.vs_memory /\ q.vs_allocas = it.vs_allocas /\
  q.vs_alloca_next = it.vs_alloca_next /\ q.vs_labels = it.vs_labels /\
  tq.t_mem = tni.t_mem /\
  (!x. not_fresh_at st2 x ==> lookup_var x q = lookup_var x it)
Proof
  simp[array_length_frame_def] >> strip_tac >>
  qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = it` mp_tac >>
  simp[venom_state_component_equality]
QED

Theorem captured_child_root_old[local]:
  local_ptrs_reserved cenv st2 /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) sz) ==>
  not_fresh_at st2 x
Proof
  simp[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem captured_child_capacity[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx r fin = (INL v,fin) /\ val_wf etv v /\
  eval_operand dst q = SOME dw /\ w2n dw = w2n (w:256 word) + j /\
  type_memory_bytes cenv et = type_memory_size etv /\
  j + type_memory_size etv <= z /\
  (z <> 0 ==> w2n w + z <= q.vs_alloca_next /\
    ?b sz. op_prov Gq dst = SOME (b,sz) /\ b <= w2n w /\ w2n w + z <= b + sz) ==>
  vv_store_bound cx et et fin r (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ptr_buf_ok cenv (Subscript et obj idx) dst Gq q
Proof
  strip_tac >>
  `val_store_size etv v <= type_memory_size etv` by simp[val_store_size_le] >>
  `type_memory_size etv <> 0 ==> w2n dw + type_memory_size etv <= q.vs_alloca_next` by
    (strip_tac >> `z <> 0` by decide_tac >> fs[] >> decide_tac) >>
  conj_tac >- (simp[vv_store_bound_def,mk_ptr_def] >> decide_tac) >>
  simp[ptr_buf_ok_def,exprLoweringTheory.lowered_value_type_def,vyperASTTheory.expr_type_def] >>
  strip_tac >> `z <> 0` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `dst` >> gvs[op_prov_def] >>
  qexistsl [`b`,`sz`] >> simp[] >> decide_tac
QED

Theorem array_captured_fixed_child_mods:
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
  popped_keys_indexed fin.scopes /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL (ArrayV (SArrayV kvs)),fin) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand it = SOME w /\
  place_ptr_rel cenv cx it (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type (ArrayT et (Fixed n))) /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) fin Gi tni it /\
  vv_at cenv cx (ArrayT et (Fixed n)) sa st2 fin (PlaceR (MemoryPlace id path))
    (LocatedValue t p) it /\
  w2n w + n * type_memory_size etv < dimword (:256) /\
  (n * type_memory_size etv <> 0 ==>
    w2n w + n * type_memory_size etv <= it.vs_alloca_next /\
    ?b sz. op_prov Gi p.ptr_operand = SOME (b,sz) /\ b <= w2n w /\
           w2n w + n * type_memory_size etv <= b + sz) /\
  0 <= i /\ Num i < n /\ iw = n2w (Num i) /\
  array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v /\
  value_has_type etv v /\ val_wf etv v /\
  read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))) fin = (INL v,fin) /\
  esz = type_memory_size etv /\ type_memory_bytes cenv et = type_memory_size etv /\
  local_ptrs_reserved cenv st2 /\ st2.cs_next_id <= sb.cs_next_id /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at st2 x) /\
  array_length_frame st2 it Gi tni q Gq tq /\
  eval_operand dst q = SOME (w + iw * n2w esz) /\
  op_prov Gq dst = op_prov Gi p.ptr_operand /\ op_taint tq dst = {} ==>
  let r' = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]));
      vv = LocatedValue et (mk_ptr dst LocMemory)
  in
    vv_at cenv cx et sa sb fin r' vv q /\
    vv_place_ptr cenv cx fin q r' vv /\ vv_holds cenv cx et r' vv fin q /\
    ptr_vv_ok cx et r' vv fin Gq tq q /\ vv_store_bound cx et et fin r' vv q /\
    ptr_buf_ok cenv (Subscript et obj idx) dst Gq q
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `j = Num i * type_memory_size etv` >>
  `j + type_memory_size etv <= n * type_memory_size etv` by
    (unabbrev_all_tac >> irule array_index_element_end_bound >> simp[]) >>
  `w2n (w + n2w j) = w2n w + j` by (irule w2n_add_n2w_lt >> decide_tac) >>
  `eval_operand dst q = SOME (w + n2w j)` by simp[Abbr `j`, word_mul_n2w] >>
  drule_then strip_assume_tac captured_child_readonly >>
  `!nm sz b. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var nm) sz) /\
     lookup_var nm it = SOME b ==> lookup_var nm q = SOME b` by
    (rpt strip_tac >> drule_all captured_child_root_old >> simp[]) >>
  `eval_operand p.ptr_operand q = eval_operand p.ptr_operand it` by
    (irule stmtSimReturnTheory.eval_operand_old_vars >> simp[] >> qexists `st2` >> simp[]) >>
  `!nm b sz. local_region cenv fin.scopes q nm b sz <=>
              local_region cenv fin.scopes it nm b sz` by
    (rpt gen_tac >> irule bop_local_region_readonly_frame >> qexists `st2` >> simp[]) >>
  `vv_at cenv cx (ArrayT et (Fixed n)) sa sb fin (PlaceR (MemoryPlace id path))
     (LocatedValue t p) q` by
    (irule vv_at_vars_frame >> qexistsl [`it`,`st2`] >> simp[vv_operand_def]) >>
  `vv_place_ptr cenv cx fin q (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
      (LocatedValue et (mk_ptr dst LocMemory)) /\
   ptr_vv_ok cx et (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
      (LocatedValue et (mk_ptr dst LocMemory)) fin Gq tq q` by
    (unabbrev_all_tac >>
     drule_all_then strip_assume_tac (REWRITE_RULE []
       (Q.INST [`j` |-> `Num i * type_memory_size etv`] subscript_captured_fixed_child)) >>
     simp[]) >>
  conj_tac
  >- (irule vv_at_fixed_array_element >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ q`)) >>
      goal_assum (drule_at (Pat `read_result _ (PlaceR (MemoryPlace id (path ++ _))) _ = _`)) >>
      goal_assum (drule_at (Pat `read_result _ _ _ = (INL (ArrayV _),_)`)) >>
      goal_assum (drule_at (Pat `evaluate_type _ et = _`)) >>
      simp[] >> qexists `i` >>
      simp[mem_step_offset_def,Abbr `j`] >>
      rpt gen_tac >> eq_tac >> strip_tac >> simp[]) >>
  simp[] >> conj_tac
  >- (simp[vv_holds_def,mk_ptr_def] >>
      `ptr_mem_ok cx et v dst Gq tq q` by
        (qpat_x_assum `ptr_vv_ok cx et _ _ fin Gq tq q` mp_tac >>
         simp[ptr_vv_ok_def,mk_ptr_def]) >>
      drule_all ptr_mem_ok_representation >> simp[] >> strip_tac >> simp[] >>
      strip_tac >> drule_all val_in_memory_word_type >> simp[]) >>
  irule captured_child_capacity >>
  goal_assum (drule_at (Pat `read_result _ (PlaceR (MemoryPlace id (path ++ _))) _ = _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ et = _`)) >>
  qexistsl [`w + n2w j`,`j`,`w`,`n * type_memory_size etv`] >> simp[]
QED
