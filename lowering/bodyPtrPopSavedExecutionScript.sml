Theory bodyPtrPopSavedExecution
Ancestors
  bodyPtrPopConsumerCut bodyPtrPopNestedLifetimeProbe vyperInterpreter
  vyperContext vyperState vyperStorageBackend exprLowering compileEnv
  vyperCompiler venomExecSemantics vyperValue

(* Names for a bounded operational experiment, not a new invariant. The
   captured target is b[1]; evaluating b.pop()[0][0] kills its global region
   without changing the saved header at slot 8. No supported-entry claim. *)
Definition pop_saved_tops_def:
  pop_saved_tops = [VariableDecl Private Storage "b"
    (ArrayT (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2))
      (Dynamic 2)) (Dynamic 2)) (SOME 0)]
End
Definition pop_saved_cx_def:
  pop_saved_cx = empty_evaluation_context with
    <| sources := [(0w,[(NONE,pop_saved_tops)])];
       layouts := [(0w,([((NONE,"b"),0)],[]))] |>
End
Definition pop_saved_store_def:
  pop_saved_store : bytes32 -> bytes32 =
    (0w =+ 2w) ((8w =+ 2w) ((9w =+ 1w) (K 0w)))
End
Definition pop_saved_es_def:
  pop_saved_es = set_storage pop_saved_cx
    (empty_state with <|scopes := [FEMPTY]; outcomes := SOME []|>) F
    pop_saved_store
End
Definition pop_saved_index_def:
  pop_saved_index = Subscript (BaseT (UintT 256))
    (Subscript (ArrayT (BaseT (UintT 256)) (Dynamic 2))
      (Pop (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Dynamic 2))
        (TopLevelNameTarget (NONE,"b")))
      (Literal (BaseT (UintT 256)) (IntL 0)))
    (Literal (BaseT (UintT 256)) (IntL 0))
End

Theorem pop_saved_source_index:
  ?es. bind (eval_expr pop_saved_cx pop_saved_index)
    (read_result pop_saved_cx) pop_saved_es = (INL (IntV 0),es) /\
    lookup_storage 0w (get_storage pop_saved_cx es F) = 1w /\
    lookup_storage 8w (get_storage pop_saved_cx es F) = 2w
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition pop_saved_cenv_def:
  pop_saved_cenv = build_compile_env pop_saved_tops Internal Nonpayable
    "probe" [] (BaseT (UintT 256)) [] F
End
Definition pop_saved_target_def:
  pop_saved_target = SubscriptTarget (TopLevelNameTarget (NONE,"b"))
    (Literal (BaseT (UintT 256)) (IntL 1))
End
Definition pop_saved_cut_def:
  pop_saved_cut = compile_get_target_ptr compile_expr pop_saved_cenv
    pop_saved_target (initial_compile_state "entry")
End
Definition pop_saved_lowered_def:
  pop_saved_lowered = lower_value compile_expr pop_saved_cenv
    (BaseT (UintT 256)) pop_saved_index (SND pop_saved_cut)
End
Definition pop_saved_code_def:
  pop_saved_code = (SND pop_saved_lowered).cs_current_insts
End
Definition pop_saved_runtime_def:
  pop_saved_runtime = sstore 0w 2w (sstore 8w 2w
    (sstore 9w 1w (init_venom_state "entry")))
End

Theorem pop_saved_runtime_index:
  ?s. run_inst_seq pop_saved_code pop_saved_runtime = OK s /\
    eval_operand (FST pop_saved_lowered) s = SOME 0w /\
    eval_operand (FST (FST pop_saved_cut)) s = SOME 8w /\
    sload 0w s = 1w /\ sload 8w s = 2w
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition pop_saved_header_def:
  pop_saved_header = compile_ptr_load F NONE LocStorage
    (FST (FST pop_saved_cut)) (SND pop_saved_lowered)
End

Theorem pop_saved_next_header:
  ?s. run_inst_seq (SND pop_saved_header).cs_current_insts
      pop_saved_runtime = OK s /\
    eval_operand (FST pop_saved_header) s = SOME 2w /\
    sload 0w s = 1w /\ sload 8w s = 2w /\
    pop_region_taint_ok
      (s.vs_accounts s.vs_call_ctx.cc_address).storage 8
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2)) {} /\
    dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage 0
      (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
        (Dynamic 2)) (Dynamic 2)) 8 0
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

