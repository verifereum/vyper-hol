(* Length and element-layout boundaries for framed array subscripts. *)
Theory exprSimSubscriptArrayFramed
Ancestors
  exprSimSubscriptArrayFrame exprSimArrayIndex exprSimLen exprSimCopy
  exprSimAggregateEncoding exprSimProps loweringPosts vyperTypeSystem arithmetic
  emitHelperProps exprLoweringProps venomExecSemantics exprLowering compileEnv
  exprSimHypsDefs supportedExprTraverse vyperTypeCallStackSoundness

(* The runtime loader of a code array's length word: a DLOAD of the data
   section at the base. *)
Theorem array_len_ok_DLOAD:
  !imm cnt base_op ss b.
    eval_operand base_op ss = SOME b ==>
    array_len_ok T cnt (compile_ptr_load F imm LocCode) base_op ss
      (word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n b) ss.vs_data_section ++ REPLICATE 32 0w)))
Proof
  rw[array_len_ok_def, contextTheory.compile_ptr_load_def,
     contextTheory.compile_imm_load_word_runtime] >>
  imp_res_tac emit_op_extends >>
  qspecl_then [`DLOAD`, `\a s. word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))`]
    mp_tac emit_op_read1_correct >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  simp[step_inst_base_def, exec_read1_def] >> strip_tac >>
  first_x_assum (qspecl_then [`b`, `ss`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem immutable_array_len_ok:
  stmt_state_rel ctx func cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT et (Dynamic bound)) r w es s /\
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es) r (Type (ArrayT et (Dynamic bound))) /\
  result_array_length cx r es = (INL n,es) /\
  eval_operand base_op s = SOME w ==>
  array_len_ok T cnt (compile_ptr_load F imm LocCode) base_op s (n2w n)
Proof
  strip_tac >> drule_all immutable_holds_data >> strip_tac >>
  `value_has_type tvt v` by gvs[immutable_holds_def] >>
  `mem_word_at (w2n w) s.vs_data_section = n2w n` by
    (irule read_result_memory_header >> simp[is_sized_type_def] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`cx`, `env`, `es`, `r`, `ArrayT et (Dynamic bound)`] >>
     simp[]) >>
  drule array_len_ok_DLOAD >>
  gvs[valueEncodingTheory.mem_word_at_def]
QED

Theorem sub_layout_array_element:
  sub_layout itv iv k (ArrayTV et bd) (ArrayV av) /\
  val_wf (ArrayTV et bd) (ArrayV av) /\
  array_index (ArrayTV et bd) av i = SOME v ==>
  sub_layout itv iv
    (k + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
     Num i * type_memory_size et) et v
Proof
  strip_tac >> Cases_on `av` >> Cases_on `bd` >>
  gvs[valueEncodingTheory.val_wf_def, vyperValueOperationTheory.array_index_def,
      AllCaseEqs(), listTheory.oEL_THM] >>
  gvs[sub_layout_def, valueEncodingTheory.type_memory_size_def]
  >~ [`ArrayV (DynArrayV vs)`]
  >- (`(Num i + 1) * type_memory_size et <= n * type_memory_size et` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      conj_tac
      >- (qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
          pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
      rpt strip_tac >> first_x_assum drule >>
      simp[valueEncodingPropsTheory.val_in_memory_dynarray] >> strip_tac >>
      drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  (`(Num i + 1) * type_memory_size et <= n * type_memory_size et` by
    (irule LESS_MONO_MULT >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!b mem. _` (qspecl_then [`b`, `mem`] mp_tac) >>
  simp[valueEncodingPropsTheory.val_in_memory_sarray] >> strip_tac >>
  metis_tac[valueEncodingProofsTheory.kvs_in_memory_lookup, ADD_ASSOC])
QED

Theorem local_path_at_step:
  local_path_at cenv cx n k tv /\ mem_step_offset tv sb = SOME (j,et) ==>
  local_path_at cenv cx n (k + j) et
Proof
  rw[local_path_at_def] >>
  qexistsl_tac [`t0`, `tv0`, `path ++ [sb]`] >> simp[] >>
  drule_all mem_path_offset_snoc >> simp[]
QED

Theorem local_val_at_array_element:
  local_val_at cenv cx n k (ArrayTV et bd) (ArrayV av) /\
  mem_step_offset (ArrayTV et bd) (ValueSubscript (IntV i)) = SOME (j,et) ==>
  local_val_at cenv cx n (k + j) et v
Proof
  simp[local_val_at_def] >> strip_tac >> disj1_tac >>
  drule_all local_path_at_step >> simp[]
QED

(* Select a typed element within the immutable's represented array. *)
Theorem immutable_holds_array_element:
  immutable_holds cenv cx (ArrayT et bd) r w es s /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  value_has_type etv v /\ read_result cx child es = (INL v,es) ==>
  immutable_holds cenv cx et child
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
              Num i * type_memory_size etv)) es s
Proof
  strip_tac >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  drule_all sub_layout_array_element >> simp[] >> strip_tac >>
  irule immutable_holds_sub >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem vv_at_fixed_array_element:
  vv_at cenv cx (ArrayT et (Fixed n)) sa sb es r (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx child es = (INL v,es) /\ val_wf etv v /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  eval_operand dst s = SOME dw /\ w2n dw = w2n w + j ==>
  vv_at cenv cx et sa sb es child (LocatedValue et (mk_ptr dst LocMemory)) s
Proof
  strip_tac >>
  `val_footprint etv v <= type_memory_size etv` by
    (irule val_footprint_le >> simp[]) >>
  `j + val_footprint etv v <= n * type_memory_size etv` by
    (gvs[mem_step_offset_def, AllCaseEqs()] >>
     `(Num i + 1) * type_memory_size etv <= n * type_memory_size etv` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  `val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) = n * type_memory_size etv` by
    simp[val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def, contextTheory.mk_ptr_def] >> strip_tac >> gvs[]
  >~ [`FLOOKUP s.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n'`, `b`, `sz`] >>
  simp[] >>
  `j + w2n w - b = (w2n w - b) + j` by decide_tac >>
  drule_all local_val_at_array_element >>
  disch_then (qspec_then `v` assume_tac) >>
  qpat_x_assum `j + w2n w - b = _` SUBST1_TAC >> first_assum ACCEPT_TAC
QED

Theorem vv_holds_array_element:
  vv_holds cenv cx (ArrayT et bd) r (LocatedValue ann p) es s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand s = SOME w /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\ value_has_type etv v /\
  read_result cx child es = (INL v,es) /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst s = SOME (w + n2w j) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) ==>
  vv_holds cenv cx et child (LocatedValue et (mk_ptr dst p.ptr_location)) es s
Proof
  strip_tac >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  drule_all sub_layout_array_element >> simp[] >> strip_tac >>
  gvs[vv_holds_def, contextTheory.mk_ptr_def]
  >~ [`p.ptr_location = LocCode`]
  >- (drule_all immutable_holds_array_element >> simp[]) >>
  conj_asm1_tac
  >- (qpat_x_assum `sub_layout _ _ _ etv v` mp_tac >>
      simp[sub_layout_def] >> metis_tac[]) >>
  strip_tac >> irule val_in_memory_word_type >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`et`, `get_tenv cx`] >> simp[]
QED

(* Expose the two child intervals and the bounds/element tail once. *)
Theorem compile_expr_array_subscript:
  compile_expr cenv ty (Subscript ann obj idx) st = (vv, st') /\
  place_type cenv obj = ValPT (ArrayT et bd) ==>
  ?bvv st1 iop st2 dst loc.
    compile_expr cenv ty obj st = (bvv, st1) /\
    lower_value compile_expr cenv ty idx st1 = (iop, st2) /\
    loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location cenv loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc)
      st2 = (dst, st') /\
    vv = LocatedValue ann (mk_ptr dst loc)
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, lower_value_def,
       exprCallBoundsTheory.expr_child_callback_def,
       comp_bind_def, comp_return_def,
       vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

