(* Shared type-layout offsets and target-place pointer relation.
   Relocated from targetPlaceSim so raw expression results can retain them. *)
Theory placeProvenance
Ancestors
  list rich_list finite_map pair exprLowering compileEnv
  valueEncoding vyperAST vyperInterpreter vyperState vyperValue
  venomState venomInst
Libs
  pairLib

Definition mem_field_offset_def:
  mem_field_offset [] id = NONE /\
  mem_field_offset ((name,tv)::fields) id =
    if name = id then SOME (0n,tv)
    else OPTION_MAP (\(off,ftv). (type_memory_size tv + off,ftv))
           (mem_field_offset fields id)
End

Definition mem_step_offset_def:
  mem_step_offset (StructTV fields) (AttrSubscript id) =
    mem_field_offset fields id /\
  mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then SOME (Num i * type_memory_size etv, etv)
     else NONE) /\
  mem_step_offset (ArrayTV etv (Dynamic n)) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < n then SOME (32 + Num i * type_memory_size etv, etv)
     else NONE) /\
  mem_step_offset (TupleTV tvs) (ValueSubscript (IntV i)) =
    (if 0 <= i /\ Num i < LENGTH tvs then
       SOME (type_memory_size_list (TAKE (Num i) tvs), EL (Num i) tvs)
     else NONE) /\
  mem_step_offset _ _ = NONE
End

Definition mem_path_offset_def:
  mem_path_offset tv [] = SOME (0n,tv) /\
  mem_path_offset tv (sb::path) =
    case mem_step_offset tv sb of
    | NONE => NONE
    | SOME (k,etv) =>
        OPTION_MAP (\(k',ptv). (k + k',ptv)) (mem_path_offset etv path)
End

Theorem mem_path_offset_snoc:
  !path tv k ptv sb k2 etv.
    mem_path_offset tv path = SOME (k,ptv) /\
    mem_step_offset ptv sb = SOME (k2,etv) ==>
    mem_path_offset tv (path ++ [sb]) = SOME (k + k2,etv)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  first_x_assum drule_all >> simp[]
QED

Theorem mem_field_offset_sound[local]:
  !fs fld k ftv.
    mem_field_offset fs fld = SOME (k,ftv) ==>
    ALOOKUP fs fld = SOME ftv /\
    k + type_memory_size ftv <= type_memory_size_fields fs
Proof
  Induct >> simp[mem_field_offset_def] >> PairCases >>
  simp[mem_field_offset_def, type_memory_size_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[PULL_EXISTS, FORALL_PROD] >>
  rpt strip_tac >> res_tac >> simp[]
QED

Theorem type_memory_size_list_take_el[local]:
  !tvs n. n < LENGTH tvs ==>
    type_memory_size_list (TAKE n tvs) + type_memory_size (EL n tvs) <=
    type_memory_size_list tvs
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `n` >>
  simp[type_memory_size_def] >> strip_tac >> res_tac >> simp[]
QED

Theorem mul_succ_le[local]:
  !i n. i < n ==> !s. i * s + s <= n * s
Proof
  rpt strip_tac >> REWRITE_TAC [GSYM arithmeticTheory.MULT] >>
  irule arithmeticTheory.LESS_MONO_MULT >> simp[]
QED

Theorem mem_step_offset_sound[local]:
  !tv sb k etv.
    mem_step_offset tv sb = SOME (k,etv) ==>
    subscript_type tv sb = SOME etv /\
    k + type_memory_size etv <= type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `tv` >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd`) >>
  simp[mem_step_offset_def, subscript_type_def, type_memory_size_def] >>
  rw[] >> gvs[] >>
  TRY (drule mem_field_offset_sound >> simp[] >> NO_TAC) >>
  TRY (drule type_memory_size_list_take_el >> simp[] >> NO_TAC) >>
  qpat_x_assum `Num _ < _` (mp_tac o MATCH_MP mul_succ_le) >>
  disch_then (qspec_then `type_memory_size etv` mp_tac) >> simp[]
QED

Theorem mem_path_offset_sound:
  !path tv k ptv.
    mem_path_offset tv path = SOME (k,ptv) ==>
    subscripts_type tv path = SOME ptv /\
    k + type_memory_size ptv <= type_memory_size tv
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, subscripts_type_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  drule mem_step_offset_sound >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[subscripts_type_def]
QED

Definition slot_loc_def:
  slot_loc tr = if tr then LocTransient else LocStorage
End

(* Original target relation, including its original immutable-F clause. *)
Definition place_ptr_rel_def:
  (place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc vt <=>
     ?p sz b t0 tv0 k tv t.
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
       lookup_var p s = SOME b /\
       cenv.ce_var_type id = SOME t0 /\
       evaluate_type (get_tenv cx) t0 = SOME tv0 /\
       mem_path_offset tv0 path = SOME (k,tv) /\
       w = b + n2w k /\ loc = SOME LocMemory /\
       vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\
     ?t. vt = Type t /\ evaluate_type (get_tenv cx) t = SOME tv) /\
  (place_ptr_rel cenv cx s (HashMapRef tr slot kt vt') w loc vt <=>
     w = slot /\ loc = SOME (slot_loc tr) /\ vt = HashMapT kt vt') /\
  (place_ptr_rel cenv cx s (PlaceR (ImmutablePlace src id path)) w loc vt <=>
     F) /\
  (place_ptr_rel cenv cx s (Value v) w loc vt <=> F)
End
