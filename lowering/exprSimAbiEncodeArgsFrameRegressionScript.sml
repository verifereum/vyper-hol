Theory exprSimAbiEncodeArgsFrameRegression
Ancestors
  loweringPosts valueEncodingProps vyperInterpreter venomState

(* The old flat witness's root, immediately before and after its pop. *)
Definition abi_flat_root_tv_def:
  abi_flat_root_tv = ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 2)
End

Definition abi_flat_initial_def:
  abi_flat_initial = empty_state with <|
    scopes := [FEMPTY |+ ("root", <|assignable := T;
      type := abi_flat_root_tv;
      value := ArrayV (DynArrayV [ArrayV (DynArrayV []); ArrayV (DynArrayV [])]);
      popped := []|>)]; outcomes := SOME []|>
End

Definition abi_flat_snapshot_def:
  abi_flat_snapshot = ([ValueSubscript (IntV 1)], ArrayV (DynArrayV []))
End

Theorem abi_flat_snapshot_overwrite:
  !b s. ~snapshot_in abi_flat_root_tv b 160 abi_flat_snapshot
    (mstore (b+96) 1w s).vs_memory
Proof
  simp[snapshot_in_def, abi_flat_root_tv_def, abi_flat_snapshot_def,
       compileEnvTheory.mem_path_offset_def, compileEnvTheory.mem_step_offset_def,
       valueEncodingTheory.type_memory_size_def, valueEncodingTheory.val_in_memory_def,
       valueEncodingPropsTheory.mstore_mem_word_at_same]
QED

Definition abi_flat_popped_def:
  abi_flat_popped = SND (eval_expr empty_evaluation_context
    (Pop (ArrayT (BaseT BoolT) (Dynamic 1)) (NameTarget "root"))
    abi_flat_initial)
End

Theorem abi_flat_pop_history:
  ?entry. lookup_scopes "root" abi_flat_popped.scopes = SOME entry /\
    entry.type = abi_flat_root_tv /\ MEM abi_flat_snapshot entry.popped
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem abi_flat_old_call_frame_excluded:
  !ce sa s b.
    local_region ce abi_flat_popped.scopes s "root" b 160 /\
    snapshot_in abi_flat_root_tv b 160 abi_flat_snapshot s.vs_memory ==>
    ~wb_frame ce abi_flat_popped abi_flat_popped sa s (mstore (b+96) 1w s)
Proof
  rpt strip_tac >>
  mp_tac abi_flat_pop_history >> strip_tac >>
  gvs[wb_frame_def, locals_kept_def, popped_kept_def] >>
  first_x_assum (qspecl_then [`"root"`, `b`, `160`, `entry`,
                             `abi_flat_snapshot`] mp_tac) >>
  simp[abi_flat_snapshot_overwrite] >>
  rpt strip_tac >>
  `entry' = entry` by metis_tac[optionTheory.SOME_11] >> gvs[]
QED

(* At the later call the root length is one and its freed second slot is
   still zero, exactly the branch on which the historical callee wrote. *)
Theorem abi_flat_snapshot_before_call:
  snapshot_in abi_flat_root_tv 0 160 abi_flat_snapshot
    (REPLICATE 31 0w ++ [1w] ++ REPLICATE 128 0w)
Proof
  simp[snapshot_in_def, abi_flat_root_tv_def, abi_flat_snapshot_def,
       compileEnvTheory.mem_path_offset_def, compileEnvTheory.mem_step_offset_def,
       valueEncodingTheory.type_memory_size_def] >> EVAL_TAC >> simp[]
QED
