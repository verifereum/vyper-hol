(* Contract probe for the effectful AugAssign dead-slot boundary.
   The motivating nested-array pop is not in the supported expression subset. *)
Theory augAssignEffectfulIndexProbe
Ancestors
  supportedExprs supportedExprForms supportedTypes supportedDecls
  supportedTargets supportedStmts supportedProgram vyperAST list
  vyperInterpreter vyperState vyperContext vyperStorage compileEnv
Libs
  wordsLib

Theorem supported_storage_pop_element_word:
  supported_expr tops (Pop ty (TopLevelNameTarget nsid)) /\
  supported_variable_decl tops nsid = SOME (vis,mut,ArrayT elem bd,slot) ==>
  supported_full_word_type elem
Proof
  strip_tac >>
  gvs[supported_expr_def, supported_pure_expr_def,
      supported_effect_expr_def, supported_storage_dynamic_array_def] >>
  Cases_on `vis` >> Cases_on `mut` >> Cases_on `bd` >>
  Cases_on `slot` >> gvs[]
QED

Theorem nested_array_pop_candidate_excluded:
  ~supported_expr
    [VariableDecl Private Storage "b"
      (ArrayT (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2))
        (Dynamic 2)) (Dynamic 2)) (SOME 0)]
    (Pop ty (TopLevelNameTarget (NONE,"b")))
Proof
  EVAL_TAC
QED

(* Unlike a nested Pop, an internal call may replace the containing array. *)
Theorem internal_call_stale_base_candidate_supported:
  let u = BaseT (UintT 256);
      arr = ArrayT (ArrayT u (Dynamic 2)) (Dynamic 2);
      body = [Assign (BaseTarget (TopLevelNameTarget (NONE,"b")))
                (Builtin arr (MakeArray (SOME (ArrayT u (Dynamic 2))) (Dynamic 2)) []);
              Return (SOME (Literal u (IntL 0)))];
      tops = [VariableDecl Private Storage "b" arr (SOME 0);
              FunctionDecl Internal NonPayable F F "shrink" [] [] u body];
      bt = SubscriptTarget
             (SubscriptTarget (TopLevelNameTarget (NONE,"b"))
               (Literal u (IntL 1)))
             (Call u (IntCall (NONE,"shrink")) [] NONE)
  in supported_function_body tops Internal [] body /\
     supported_stmt tops [] (AugAssign u bt Add (Literal u (IntL 1))) /\
     ~supported_target_pure tops bt
Proof
  EVAL_TAC
QED

Theorem internal_call_stale_base_source_read:
  let u = BaseT (UintT 256);
      arr = ArrayT (ArrayT u (Dynamic 2)) (Dynamic 2);
      body = [Assign (BaseTarget (TopLevelNameTarget (NONE,"b")))
                (Builtin arr (MakeArray (SOME (ArrayT u (Dynamic 2))) (Dynamic 2)) []);
              Return (SOME (Literal u (IntL 0)))];
      tops = [VariableDecl Private Storage "b" arr (SOME 0);
              FunctionDecl Internal NonPayable F F "shrink" [] [] u body];
      cx = empty_evaluation_context with
             <|sources := [(0w,[(NONE,tops)])];
               layouts := [(0w, ( [((NONE,"b"),0)], [] ))]|>;
      raw = (\k:bytes32. if k = 0w then 2w else
                         if k = 4w then 1w else
                         if k = 5w then 7w else 0w);
      initial = SND (set_storage_backend cx F raw empty_state);
      bt = SubscriptTarget
             (SubscriptTarget (TopLevelNameTarget (NONE,"b"))
               (Literal u (IntL 1)))
             (Call u (IntCall (NONE,"shrink")) [] NONE);
      result = eval_target_place cx bt initial
  in ?st. result = (INL (StoragePlace F 5w (BaseTV (UintT 256))), st) /\
          read_place cx (StoragePlace F 5w (BaseTV (UintT 256))) st =
            (INL (IntV 7),st) /\
          dead_bytes (get_storage cx st F) 0
            (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2)) 5 0
Proof
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  qexists_tac `1` >> simp[]
QED

(* The nonempty replacement proposed for a raw-copy contrast makes the
   subsequent subscript fail: the saved inner base now has length zero. *)
Theorem nonempty_replacement_candidate_bounds_error:
  let u = BaseT (UintT 256);
      inner = ArrayT u (Dynamic 2);
      arr = ArrayT inner (Dynamic 2);
      empty = Builtin inner (MakeArray (SOME u) (Dynamic 2)) [];
      body = [Assign (BaseTarget (TopLevelNameTarget (NONE,"b")))
                (Builtin arr (MakeArray (SOME inner) (Dynamic 2)) [empty;empty]);
              Return (SOME (Literal u (IntL 0)))];
      tops = [VariableDecl Private Storage "b" arr (SOME 0);
              FunctionDecl Internal NonPayable F F "shrink" [] [] u body];
      cx = empty_evaluation_context with
             <|sources := [(0w,[(NONE,tops)])];
               layouts := [(0w, ( [((NONE,"b"),0)], [] ))]|>;
      raw = (\k:bytes32. if k = 0w then 2w else
                         if k = 4w then 1w else
                         if k = 5w then 7w else 0w);
      initial = SND (set_storage_backend cx F raw empty_state);
      bt = SubscriptTarget
             (SubscriptTarget (TopLevelNameTarget (NONE,"b"))
               (Literal u (IntL 1)))
             (Call u (IntCall (NONE,"shrink")) [] NONE)
  in supported_function_body tops Internal [] body /\
     supported_stmt tops [] (AugAssign u bt Add (Literal u (IntL 1))) /\
     FST (eval_target_place cx bt initial) =
       INR (Error (RuntimeError "array dynamic length oob"))
Proof
  EVAL_TAC >>
  simp[SF wordsLib.SIZES_ss, vyperValueTheory.type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED
