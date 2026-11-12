(* Live dynamic headers and capacity bounds, independent of the instruction
   position at which the compiler reads them. *)
Theory bodyPtrBopInHeaderContents
Ancestors bodyPtrBopInCodeContents bodyPtrBopInSlotContents
  bodyPtrBopInLiveMemory bodyPtrBopInLiveStorage bodyPtrBopInRepresentation
  bodyPtrBopInSlotLoad exprSimCopy bodyPtrDefs exprSimProps valueEncodingProps
  valueEncoding valueEncodingDefs vyperValue vyperValueOperation vyperTyping loweringPosts arithmetic
  venomExecSemantics venomState ptrDiscipline

Theorem membership_dynamic_memory_header:
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) /\
  val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV av) off mem ==>
  mem_word_at off mem = n2w (array_length (ArrayTV et (Dynamic cap)) av) /\
  array_length (ArrayTV et (Dynamic cap)) av <= cap
Proof
  Cases_on `av` >>
  simp[value_has_type_def, val_in_memory_dynarray, array_length_def]
QED

Theorem membership_fixed_array_length:
  value_has_type (ArrayTV et (Fixed cap)) (ArrayV av) ==>
  array_length (ArrayTV et (Fixed cap)) av = cap
Proof
  Cases_on `av` >> simp[value_has_type_def, array_length_def]
QED

Theorem membership_dynamic_code_header:
  stmt_state_rel ctx fn cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT ety (Dynamic cap)) (Value (ArrayV av)) bw es s /\
  evaluate_type (get_tenv cx) ety = SOME et /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV av) ==>
  word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n bw) s.vs_data_section ++ REPLICATE 32 0w)) =
    n2w (array_length (ArrayTV et (Dynamic cap)) av) /\
  array_length (ArrayTV et (Dynamic cap)) av <= cap
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ety (Dynamic cap)) =
    SOME (ArrayTV et (Dynamic cap))` by
    fs[immutable_holds_def, evaluate_type_def, AllCaseEqs()] >>
  drule_all immutable_holds_data >> strip_tac >>
  gvs[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  drule_all membership_dynamic_memory_header >>
  simp[mem_word_at_def, mem_bytes_at_def]
QED

Theorem membership_located_memory_header:
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var src /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  ~is_word_type aty /\ lookup_var src s = SOME bw ==>
  ptr_covers G tn src s 32 /\ mem_word_taint tn.t_mem (w2n bw) = {} /\
  mload (w2n bw) s = n2w (LENGTH vs) /\ LENGTH vs <= cap
Proof
  strip_tac >>
  `ptr_mem_ok cx aty (ArrayV (DynArrayV vs)) (Var src) G tn s` by
    (fs[ptr_vv_ok_def] >> metis_tac[]) >>
  `eval_operand (Var src) s = SOME bw` by simp[eval_operand_def] >>
  `mem_word_taint tn.t_mem (w2n bw) = {}` by
    metis_tac[memory_dynamic_header_clean] >>
  `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
    (w2n bw) s.vs_memory` by
    gvs[ptr_mem_ok_def, mem_agree_outside_def] >>
  drule_all membership_dynamic_memory_header >>
  simp[array_length_def, mem_word_at_eq_mload] >> strip_tac >> simp[] >>
  irule (SRULE [] (Q.INST [`off` |-> `0`] membership_memory_offset_covers)) >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `vv_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[val_footprint_def, type_memory_size_def] >>
  qexistsl_tac [`fn`, `ctx`] >> simp[] >>
  fs[ptr_vv_ok_def, wordsTheory.WORD_ADD_0]
QED

Theorem membership_located_slot_header:
  storage_holds cx tr (ArrayT ety (Dynamic cap)) tvv bw es s /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  eval_operand p.ptr_operand s = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) ety = SOME tv ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) bw = {} /\
  (if tr then tload bw s else sload bw s) =
    n2w (array_length (ArrayTV tv (Dynamic cap)) av) /\
  array_length (ArrayTV tv (Dynamic cap)) av <= cap
Proof
  strip_tac >> drule_all membership_storage_array_length >> strip_tac >> simp[] >>
  irule located_dynamic_header_clean >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  fs[storage_holds_def, evaluate_type_def]
QED

Theorem membership_evaluated_dynamic_capacity_bound:
  evaluate_type tenv (ArrayT ety (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) ==>
  cap < dimword(:256)
Proof
  simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
  fs[type_slot_size_def] >> Cases_on `type_slot_size tv` >>
  gvs[MULT_CLAUSES] >> decide_tac
QED
