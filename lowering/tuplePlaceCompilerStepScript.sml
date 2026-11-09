(* Compiler-facing adapter for the nonrecursive tuple store clause. *)
Theory tuplePlaceCompilerStep
Ancestors
  tuplePlaceStep stmtLowering

Theorem tuple_place_compiler_head_step:
  tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ supported_target_pure tops bt /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  (!j. j < LENGTH tys /\ ~is_word_type (EL j tys) ==>
    type_memory_size (EL j tvs)+64 < dimword (:256) /\
    type_memory_size (EL j ltvs)+64 < dimword (:256)) /\
  (EXISTS (\t. ~is_word_type t) ltys ==> cenv.ce_target CapMcopy) /\
  type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys /\
  (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dty = case dst_ty_opt of SOME (ValPT t) => t | _ => EL i ltys;
       arr = case dty of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
         | _ => NONE
   in (if is_word_type (EL i ltys) then
         if is_word_type dty then
           compile_store_at_loc cenv.ce_imm_alloca dst (EL i elems) loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc (EL i elems) (is_word_type dty)
         NONE dty (EL i ltys) arr (type_memory_bytes cenv dty)) sa) = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ local_ptrs_reserved cenv sa /\
  write_place cx p (EL i vs) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    tuple_place_head ctx func cenv cx ff lo sb tys ltys ltvs vs elems w (SUC i) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee s /\
   (?dw. eval_operand (FST r) s = SOME dw /\
     place_ptr_rel cenv cx s (PlaceR p) dw (FST (SND r)) (Type (EL i tys))) /\
   SND (SND r) = SOME (ValPT (EL i tys)) /\
   (!x. FST r = Var x ==> not_fresh_at sa x)` by
    fs[loweringPostsTheory.target_post_def, exprLoweringTheory.value_type_place_def] >>
  `?loc. FST (SND r) = SOME loc /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient)` by
    (Cases_on `p` >> fs[loweringPostsTheory.place_ptr_rel_def] >>
     Cases_on `b` >> fs[loweringPostsTheory.slot_loc_def]) >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_index_fit >> strip_tac >>
  irule tuple_place_head_step >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `eval_operand _ _ = SOME _` (irule_at Any) >>
  qpat_assum `target_pre _ _ _ _ _` (irule_at Any) >>
  simp[] >> qexistsl [`tops`, `NONE`, `loc`] >>
  Cases_on `is_word_type (EL i ltys)` >>
  fs[stmtLoweringTheory.compile_store_at_loc_def]
QED
