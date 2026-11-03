Theory bodySimAugPlaceStorageProbe
Ancestors
  bodySimAugPlaceLoad supportedExprs supportedTargets supportedProgram
  vyperStorageBackend vyperLookupStorage compileEnv
  vyperInterpreter vyperState vyperStorage vyperValue vyperAST finite_map words
  compileVyper moduleLowering stmtLowering venomExecSemantics venomState vfmState

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

Definition aug_place_probe_ty_def:
  aug_place_probe_ty = ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1)
End

Definition aug_place_probe_body_def:
  aug_place_probe_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer")))
       (Builtin aug_place_probe_ty
          (MakeArray (SOME (ArrayT (BaseT (UintT 256)) (Fixed 1))) (Dynamic 1)) []);
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
End

Definition aug_place_probe_tops_def:
  aug_place_probe_tops =
    [VariableDecl Private Storage "outer" aug_place_probe_ty (SOME 0);
     FunctionDecl Internal Nonpayable F F "key" [] [] (BaseT (UintT 256))
       aug_place_probe_body]
End

Theorem aug_place_probe_supported:
  supported_program aug_place_probe_tops
Proof
  EVAL_TAC
QED

Definition aug_place_probe_cx_def:
  aug_place_probe_cx = empty_evaluation_context with
    <| stk := [(NONE,"caller")];
       sources := [(0w,[(NONE,aug_place_probe_tops)])];
       layouts := [(0w,([((NONE,"outer"),0)],[]))] |>
End

Definition aug_place_probe_initial_def:
  aug_place_probe_initial = empty_state with accounts :=
    (0w =+ (empty_account_state with storage :=
       (0w =+ 1w) ((1w =+ 7w) (K 0w)))) empty_accounts
End

Definition aug_place_probe_key_def:
  aug_place_probe_key = Call (BaseT (UintT 256)) (IntCall (NONE,"key")) [] NONE
End

Theorem aug_place_probe_key_source:
  let (r,s) = eval_expr aug_place_probe_cx aug_place_probe_key aug_place_probe_initial in
    r = INL (Value (IntV 0)) /\
    get_storage aug_place_probe_cx s F 0w = 0w /\
    get_storage aug_place_probe_cx s F 1w = 7w
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Definition aug_place_probe_target_def:
  aug_place_probe_target = SubscriptTarget
    (SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
      (Literal (BaseT (UintT 256)) (IntL 0))) aug_place_probe_key
End

Theorem aug_place_probe_target_source:
  let (r,s) = eval_target_place aug_place_probe_cx aug_place_probe_target
                aug_place_probe_initial in
    r = INL (StoragePlace F 1w (BaseTV (UintT 256))) /\
    get_storage aug_place_probe_cx s F 0w = 0w /\
    read_place aug_place_probe_cx (StoragePlace F 1w (BaseTV (UintT 256))) s =
      (INL (IntV 7),s)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, wordsTheory.WORD_ADD_0]
QED

Definition aug_place_probe_cenv_def:
  aug_place_probe_cenv = build_compile_env aug_place_probe_tops
    Internal Nonpayable "key" [] (BaseT (UintT 256)) aug_place_probe_body F
End

Definition aug_place_probe_lowered_def:
  aug_place_probe_lowered = SND (compile_stmt aug_place_probe_cenv NoLoop
    (BaseT (UintT 256)) (HD aug_place_probe_body) (initial_compile_state "entry"))
End

Theorem aug_place_probe_lowered_shape:
  MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
    aug_place_probe_lowered.cs_current_insts = [(SSTORE,[Lit 0w; Lit 0w],[])]
Proof
  EVAL_TAC
QED

Theorem aug_place_probe_lowered_step:
  step_inst_base (HD aug_place_probe_lowered.cs_current_insts) s =
    OK (sstore 0w 0w s)
Proof
  EVAL_TAC
QED

Theorem aug_place_probe_lowered_words:
  contract_storage s = (0w =+ 1w) ((1w =+ 7w) (K 0w)) ==>
  sload 0w (sstore 0w 0w s) = 0w /\
  sload 1w (sstore 0w 0w s) = 7w
Proof
  strip_tac >>
  simp[sload_def, sstore_def, contract_storage_def,
       lookup_account_def, update_storage_def, lookup_storage_def] >>
  EVAL_TAC >> gvs[contract_storage_def, lookup_account_def] >> EVAL_TAC >> simp[]
QED

Definition aug_place_probe_env_def:
  aug_place_probe_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY |+ ((NONE,"outer"),Type aug_place_probe_ty);
    type_defs := type_env aug_place_probe_tops;
    fn_sigs := FEMPTY |+ ((NONE,"key"),
      <|param_types := []; num_defaults := 0; ret_ty := BaseT (UintT 256)|>);
    flag_members := FEMPTY |>
End

Theorem aug_place_probe_body_typed:
  IS_SOME (type_stmts aug_place_probe_env (BaseT (UintT 256)) aug_place_probe_body)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def]
QED

Theorem aug_place_probe_target_admitted:
  supported_target_info aug_place_probe_tops [] aug_place_probe_target =
    SOME (ValPT (BaseT (UintT 256))) /\
  type_place_target aug_place_probe_env aug_place_probe_target =
    SOME (Type (BaseT (UintT 256)))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem aug_place_probe_augassign_admitted:
  supported_stmt aug_place_probe_tops []
    (AugAssign (BaseT (UintT 256)) aug_place_probe_target Add
      (Literal (BaseT (UintT 256)) (IntL 1))) /\
  IS_SOME (type_stmt aug_place_probe_env (BaseT (UintT 256))
    (AugAssign (BaseT (UintT 256)) aug_place_probe_target Add
      (Literal (BaseT (UintT 256)) (IntL 1))))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def] >> EVAL_TAC >> simp[]
QED

Definition aug_place_probe_function_def:
  aug_place_probe_function = SND (compile_internal_function aug_place_probe_cenv
    [] F F 0 F F F 0 aug_place_probe_body (SOME (BaseT (UintT 256)))
    (initial_compile_state "entry"))
End

Theorem aug_place_probe_function_shape:
  MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
    aug_place_probe_function.cs_current_insts =
      [(RETPC_PARAM,[Lit 0w],["%0"]); (ALLOCA,[Lit 32w],["%1"]);
       (SSTORE,[Lit 0w; Lit 0w],[]); (RET,[Lit 0w; Var "%0"],[])]
Proof
  EVAL_TAC >> simp[]
QED

(* Nested-copy probe: a live outer element contains an empty inner array. *)
Definition aug_place_nested_ty_def:
  aug_place_nested_ty = ArrayT aug_place_probe_ty (Dynamic 1)
End

Definition aug_place_nested_rhs_def:
  aug_place_nested_rhs = Builtin aug_place_nested_ty
    (MakeArray (SOME aug_place_probe_ty) (Dynamic 1))
    [Builtin aug_place_probe_ty
      (MakeArray (SOME (ArrayT (BaseT (UintT 256)) (Fixed 1))) (Dynamic 1)) []]
End

Definition aug_place_nested_body_def:
  aug_place_nested_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer"))) aug_place_nested_rhs;
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
End

Definition aug_place_nested_tops_def:
  aug_place_nested_tops =
    [VariableDecl Private Storage "outer" aug_place_nested_ty (SOME 0);
     FunctionDecl Internal Nonpayable F F "key" [] [] (BaseT (UintT 256))
       aug_place_nested_body]
End

Theorem aug_place_nested_supported:
  supported_program aug_place_nested_tops
Proof
  EVAL_TAC
QED

Definition aug_place_nested_env_def:
  aug_place_nested_env = aug_place_probe_env with
    <| toplevel_vtypes := FEMPTY |+ ((NONE,"outer"),Type aug_place_nested_ty);
       type_defs := type_env aug_place_nested_tops |>
End

Theorem aug_place_nested_typed:
  IS_SOME (type_stmts aug_place_nested_env (BaseT (UintT 256)) aug_place_nested_body)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def]
QED

Definition aug_place_nested_cenv_def:
  aug_place_nested_cenv = build_compile_env aug_place_nested_tops
    Internal Nonpayable "key" [] (BaseT (UintT 256)) aug_place_nested_body F
End

Definition aug_place_nested_lowered_def:
  aug_place_nested_lowered = SND (compile_stmt aug_place_nested_cenv NoLoop
    (BaseT (UintT 256)) (HD aug_place_nested_body) (initial_compile_state "entry"))
End

Theorem aug_place_nested_copy_selected:
  MAP (\i. i.inst_opcode)
    (EL 1 aug_place_nested_lowered.cs_blocks).bb_instructions =
    [MUL; ADD; MLOAD; ADD; SSTORE; ADD; ASSIGN; JMP] /\
  MAP (\i. i.inst_opcode)
    (EL 5 aug_place_nested_lowered.cs_blocks).bb_instructions =
    [ALLOCA; MSTORE; ALLOCA; MSTORE; ADD; MCOPY; MLOAD; ASSIGN; JMP]
Proof
  EVAL_TAC
QED
