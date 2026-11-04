(* Diagnostic only: the merged Pop action now evaluates target indices.
   This does not refute body_intcall_case. *)
Theory bodyIntCallPopProbe
Ancestors
  bodyIntCallLabelFrame exprLowering context compileEnv emitHelper list finite_map

Theorem pop_erasing_callback_same:
  !ce bfn tfn ty st tail.
    compile_expr_body
      (\ce ty e st. (StackValue ty (Lit 0w), st with cs_blocks := []))
      bfn tfn (ce with ce_vars := FEMPTY) ty
      (Pop (BaseT (UintT 256))
        (SubscriptTarget (NameTarget "x")
          (Literal (BaseT (UintT 256)) (IntL 0))))
      (st with cs_blocks := st.cs_blocks ++ tail) =
    compile_expr_body
      (\ce ty e st. (StackValue ty (Lit 0w), st with cs_blocks := []))
      bfn tfn (ce with ce_vars := FEMPTY) ty
      (Pop (BaseT (UintT 256))
        (SubscriptTarget (NameTarget "x")
          (Literal (BaseT (UintT 256)) (IntL 0)))) st
Proof
  simp[compile_expr_body_def, compile_get_target_ptr_def,
       lower_value_def, unwrap_value_def, comp_bind_def, comp_return_def]
QED

Theorem pop_erasing_callback_not_block_tail:
  !ce bfn tfn ty.
    ~compiler_block_tail (compile_expr_body
      (\ce ty e st. (StackValue ty (Lit 0w), st with cs_blocks := []))
      bfn tfn (ce with ce_vars := FEMPTY) ty
      (Pop (BaseT (UintT 256))
        (SubscriptTarget (NameTarget "x")
          (Literal (BaseT (UintT 256)) (IntL 0)))))
Proof
  rpt gen_tac >> rewrite_tac[compiler_block_tail_def] >> strip_tac >>
  first_x_assum (qspecl_then [`[ARB]`, `ARB`]
    (mp_tac o AP_TERM ``\p : vyper_value # compile_state. LENGTH (SND p).cs_blocks``)) >>
  simp[pop_erasing_callback_same]
QED
