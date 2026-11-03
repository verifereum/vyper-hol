Theory bodySimAugPlaceStorageProbe
Ancestors
  bodySimAugPlaceLoad supportedExprs supportedTargets
  vyperStorageBackend vyperLookupStorage compileEnv
  vyperInterpreter vyperState vyperStorage vyperValue vyperAST finite_map words

(* A fixed child address is still extendable after the enclosing dynamic
   array's length has become zero. These are primitive semantic witnesses,
   not a counterexample to the final statement simulation theorem. *)
Theorem aug_place_captured_child_extend:
  extend_storage_place cx F 1w (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
    (ValueSubscript (IntV 0)) s =
    (INL (StoragePlace F 1w (BaseTV (UintT 256))),s)
Proof
  EVAL_TAC >> simp[return_def]
QED

Theorem aug_place_dead_child_bytes:
  dead_bytes (K 0w) 0
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1)) 1 0 /\
  ~dead_bytes (K 0w) 1 (BaseTV (UintT 256)) 1 0
Proof
  EVAL_TAC >> simp[return_def]
QED

Theorem aug_place_dead_child_read:
  get_storage cx s F = (K 0w) ==>
  read_place cx (StoragePlace F 1w (BaseTV (UintT 256))) s = (INL (IntV 0),s)
Proof
  strip_tac >>
  simp[read_place_def, read_storage_slot_def, get_storage_backend_eq, bind_def] >>
  EVAL_TAC >> simp[return_def]
QED

Theorem aug_place_effectful_call_key:
  supported_expr tops (Call (BaseT (UintT 256)) (IntCall id) [] NONE) <=>
  IS_SOME (supported_function_decl tops id Internal)
Proof
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem aug_place_capture_outer_child:
  get_storage cx s F = (0w =+ 1w) (K 0w) ==>
  extend_storage_place cx F 0w
    (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1))
    (ValueSubscript (IntV 0)) s =
    (INL (StoragePlace F 1w (ArrayTV (BaseTV (UintT 256)) (Fixed 1))),s)
Proof
  strip_tac >>
  simp[extend_storage_place_def, resolve_array_element_def,
       get_storage_backend_eq, bind_def, ignore_bind_def, check_def,
       assert_def, return_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem aug_place_dead_child_in_range:
  slots_in_range (K 0w) 1 (BaseTV (UintT 256))
Proof
  EVAL_TAC >> simp[]
QED

Theorem aug_place_dead_child_not_live:
  declared_storage_region cx mid n [] = SOME (F,0w,
    ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1)) /\
  (!mid' n' subs' slot' tv'.
     declared_storage_region cx mid' n' subs' = SOME (F,slot',tv') /\
     (slot',tv') <>
       (0w,ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1)) ==>
     ranges_disjoint 0 2 (w2n slot') (type_slot_size tv')) ==>
  ~storage_read_live cx F (K 0w) 1w (BaseTV (UintT 256))
Proof
  rpt strip_tac >>
  `storage_dead cx F (K 0w) 1 0` by
    (simp[storage_dead_def] >>
     qexistsl_tac [`mid`,`n`,`[]`,`0w`,
       `ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1)) (Dynamic 1)`] >>
     simp[type_slot_size_def, aug_place_dead_child_bytes, wordsTheory.dimword_def] >>
     gvs[] >> metis_tac[]) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  simp[storage_read_live_def] >>
  qexistsl_tac [`1`,`0`] >>
  simp[type_slot_size_def, aug_place_dead_child_bytes]
QED

(* This explicitly exposes the remaining execution premise: an index which
   returns zero after changing storage. No existence of such an index, or
   of all the frozen simulation premises, is claimed here. *)
Theorem aug_place_captured_target_after_key:
  eval_base_place cx bt s =
    (INL (PlaceR (StoragePlace F 1w
      (ArrayTV (BaseTV (UintT 256)) (Fixed 1)))),s1) /\
  eval_expr cx k s1 = (INL (Value (IntV 0)),s2) ==>
  eval_target_place cx (SubscriptTarget bt k) s =
    (INL (StoragePlace F 1w (BaseTV (UintT 256))),s2)
Proof
  strip_tac >>
  simp[evaluate_def, bind_def, read_result_def, return_def,
       extend_place_def, aug_place_captured_child_extend, get_place_def]
QED
