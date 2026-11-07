(* Reachability schema for the containing nested replacement audit.
   These syntax checks do not assert the frozen simulation premises. *)
Theory augAssignNestedReachProbe
Ancestors
  supportedStmts supportedTargets supportedExprs supportedExprForms
  augAssignSavedCopyBoundary augAssignCopyFootprint targetPlaceSim stmtSimDefs vyperState vyperInterpreter vyperValueOperation
  vyperContext vyperStorageBackend vfmState vyperTypeSystem finite_map

Definition nested_reach_fixed_ty_def:
  nested_reach_fixed_ty = ArrayT (BaseT (UintT 256)) (Fixed 1)
End
Definition nested_reach_inner_ty_def:
  nested_reach_inner_ty = ArrayT nested_reach_fixed_ty (Dynamic 1)
End
Definition nested_reach_outer_ty_def:
  nested_reach_outer_ty = ArrayT nested_reach_inner_ty (Dynamic 1)
End
Definition nested_reach_replacement_def:
  nested_reach_replacement = Builtin nested_reach_outer_ty
    (MakeArray (SOME nested_reach_inner_ty) (Dynamic 1))
    [Builtin nested_reach_inner_ty
      (MakeArray (SOME nested_reach_fixed_ty) (Dynamic 1)) []]
End
Definition nested_reach_body_def:
  nested_reach_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"a"))) nested_reach_replacement;
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
End
Definition nested_reach_tops_def:
  nested_reach_tops =
    [VariableDecl Private Storage "a" nested_reach_outer_ty (SOME 0);
     FunctionDecl Internal Nonpayable F F "f" [] [] (BaseT (UintT 256))
       nested_reach_body]
End
Definition nested_reach_target_def:
  nested_reach_target = SubscriptTarget
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
        (Literal (BaseT (UintT 256)) (IntL 0)))
      (Literal (BaseT (UintT 256)) (IntL 0)))
    (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE)
End

Theorem nested_reach_syntax:
  supported_storage_type nested_reach_tops nested_reach_outer_ty /\
  supported_stmts nested_reach_tops [] nested_reach_body /\
  supported_stmt nested_reach_tops []
    (AugAssign (BaseT (UintT 256)) nested_reach_target Add
      (Literal (BaseT (UintT 256)) (IntL 1))) /\
  ~supported_target_pure nested_reach_tops nested_reach_target
Proof
  EVAL_TAC >> simp[]
QED

(* The replacement can leave the saved fixed element outside the live inner
   length. This equation concerns source target evaluation only. *)
Theorem nested_reach_source_target:
  lookup_global cx NONE "a" es =
    (INL (PlaceR (StoragePlace F 0w
      (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
        (Dynamic 1)) (Dynamic 1)))), es) /\
  get_storage_backend cx F es = (INL st,es) /\
  lookup_storage 0w st = 1w /\ lookup_storage 1w st = 1w /\
  eval_expr cx (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE) es =
    (INL (Value (IntV 0)), post) ==>
  eval_target_place cx nested_reach_target es =
    (INL (StoragePlace F 2w (BaseTV (UintT 256))),post)
Proof
  strip_tac >>
  simp[nested_reach_target_def, Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[bind_def, read_result_def, return_def, extend_place_def,
       extend_storage_place_def, resolve_array_element_def,
       ignore_bind_def, check_def, assert_def, get_place_def,
       vyperValueTheory.type_slot_size_def] >>
  simp[Once evaluate_def] >>
  simp[bind_def, read_result_def, return_def, extend_place_def,
       extend_storage_place_def, resolve_array_element_def,
       ignore_bind_def, check_def, assert_def, get_place_def,
       evaluate_literal_def, vyperValueTheory.type_slot_size_def,
       SF wordsLib.SIZES_ss]
QED

Definition nested_reach_cx_def:
  nested_reach_cx = empty_evaluation_context with
    <|sources := [(0w,[(NONE,nested_reach_tops)])];
      layouts := [(0w,([((NONE,"a"),0)],[]))]|>
End
Definition nested_reach_es_def:
  nested_reach_es = SND (set_storage_backend nested_reach_cx F
    (\k:bytes32. if k = 0w then 1w else if k = 1w then 1w
       else if k = 2w then 7w else 0w) empty_state)
End

Theorem nested_reach_source_execution:
  ?post.
    eval_target_place nested_reach_cx nested_reach_target nested_reach_es =
      (INL (StoragePlace F 2w (BaseTV (UintT 256))),post) /\
    read_place nested_reach_cx (StoragePlace F 2w (BaseTV (UintT 256))) post =
      (INL (IntV 7),post) /\
    lookup_storage 0w (get_storage nested_reach_cx post F) = 1w /\
    lookup_storage 1w (get_storage nested_reach_cx post F) = 0w
Proof
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[return_def, get_place_def, combinTheory.APPLY_UPDATE_THM] >>
  EVAL_TAC
QED

Theorem nested_reach_replacement_encoding:
  encode_value
    (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 1))
      (Dynamic 1)) (Dynamic 1))
    (ArrayV (DynArrayV [ArrayV (DynArrayV [])])) =
    SOME [(0,1w);(1,0w)]
Proof
  EVAL_TAC
QED

(* This is the actual outer copy footprint, with its padding word symbolic. *)
Theorem nested_reach_copy_word:
  store_copy_normalize s t = store_copy_prefix LocStorage buf 0w s 3 ==>
  sload 2w t = mload (w2n (buf+64w)) s
Proof
  strip_tac >>
  drule (SRULE [] (Q.INST [`tr` |-> `F`, `k` |-> `0w`, `n` |-> `3`]
    normalized_copy_prefix_footprint)) >>
  simp[SF wordsLib.SIZES_ss] >>
  disch_then (qspec_then `2w` mp_tac) >>
  simp[]
QED

Definition nested_reach_env_def:
  nested_reach_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY;
    bare_global_assignable := FEMPTY |+ ((NONE,"a"),nested_reach_outer_ty);
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY |+ ((NONE,"f"),
      <|param_types := []; num_defaults := 0; ret_ty := BaseT (UintT 256)|>);
    flag_members := FEMPTY; event_fields := FEMPTY|>
End

Theorem nested_reach_typing:
  type_stmt nested_reach_env NoneT
    (AugAssign (BaseT (UintT 256)) nested_reach_target Add
      (Literal (BaseT (UintT 256)) (IntL 1))) = SOME nested_reach_env /\
  type_stmts nested_reach_env (BaseT (UintT 256)) nested_reach_body =
    SOME nested_reach_env
Proof
  EVAL_TAC >> simp[subscript_vtype_def] >> EVAL_TAC
QED
