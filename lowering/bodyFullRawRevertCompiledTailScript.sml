(* Compiler-to-joint-path boundary for the RawRevert suffix. *)
Theory bodyFullRawRevertCompiledTail
Ancestors
  bodyFullRawRevertOperand bodyFullRawRevertTail exprOperandVar
  builtinSystem emitHelper compileEnv exprSimMemDefs loweringPosts
  valueEncodingProofs vyperValue valueEncodingDefs rich_list
  exprSimProps fragExec loweringStateRelDefs exprLoweringProps
  venomState venomExecSemantics
Libs
  pairLib

Theorem raw_revert_compiled_tail_joint:
  !H ctx func cenv cx e es (sa:compile_state) (sm:compile_state)
   (sb:compile_state) (s0:venom_state) ee bs op (t:venom_state)
   cap G tn D lo d explicit PG.
  compile_raw_revert op sm = ((),sb) /\ fn_has_code sm sb func /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~t.vs_halted /\ ~ctx_has_dalloca ctx /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  expr_post H ctx func cenv cx e es sa sm s0 ee (BytesV bs) op t /\
  expr_store_bound cx (expr_type e) (BytesV bs) op t /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  ptr_val_ok cx (post_value_type cenv e) (BytesV bs) op G tn t /\
  ghost_inv_at D lo d cenv cx ee G tn t ==>
  ?w G' tn'. !D'.
    gas_origin_ptr_path (D',lo,explicit,ctx,func,PG)
      (t,G,tn) [] (Abort Revert_abort w,G',tn')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all raw_revert_data_boundary >> strip_tac >>
  `b + 32 + LENGTH bs <= t.vs_alloca_next` by
    (mp_tac (Q.SPECL [`BaseTV (BytesT (Dynamic cap))`, `BytesV bs`]
       val_footprint_le_store_size) >>
     gvs[expr_store_bound_def, evaluate_type_def, is_word_type_def,
         val_footprint_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `same_blocks sm sb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id MLOAD [op]
        [STRING #"%" (toString sm.cs_next_var)];
      mk_inst (sm.cs_next_id + 1) ADD [op; Lit 32w]
        [STRING #"%" (toString (sm.cs_next_var + 1))];
      mk_inst (sm.cs_next_id + 2) REVERT
        [Var (STRING #"%" (toString (sm.cs_next_var + 1)));
         Var (STRING #"%" (toString sm.cs_next_var))] []]` by
    (qpat_x_assum `compile_raw_revert _ _ = _` mp_tac >>
     simp[compile_raw_revert_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, same_blocks_def, APPEND_ASSOC] >>
     strip_tac >> gvs[APPEND_ASSOC]) >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts = sm.cs_current_insts ++ new` >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
     !i. i < LENGTH new ==>
       get_instruction bb (LENGTH sm.cs_current_insts + i) = SOME (EL i new)` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> gvs[same_blocks_def]) >>
  qabbrev_tac `len = STRING #"%" (toString sm.cs_next_var)` >>
  qabbrev_tac `start = STRING #"%" (toString (sm.cs_next_var + 1))` >>
  `x <> len /\ x <> start /\ len <> start` by
    (gvs[not_fresh_at_def, Abbr `len`, Abbr `start`] >>
     metis_tac[arithmeticTheory.NOT_LESS, ASCIInumbersTheory.toString_11,
               arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_LESS_SUC]) >>
  `get_instruction bb t.vs_inst_idx =
     SOME (mk_inst sm.cs_next_id MLOAD [op] [len]) /\
   get_instruction bb (SUC t.vs_inst_idx) =
     SOME (mk_inst (sm.cs_next_id + 1) ADD [op; Lit 32w] [start]) /\
   get_instruction bb (SUC (SUC t.vs_inst_idx)) =
     SOME (mk_inst (sm.cs_next_id + 2) REVERT [Var start; Var len] [])` by
    (qpat_x_assum `!i. i < LENGTH new ==> _` (fn th =>
       map_every (fn n => qspec_then n assume_tac th) [`0`, `1`, `2`]) >>
     gvs[Abbr `new`, arithmeticTheory.ADD1]) >>
  irule raw_revert_tail_joint >>
  simp[] >>
  qexistsl_tac [`sm.cs_next_id`, `len`, `LENGTH bs`, `n2w b`,
                `root`, `x`, `start`, `sz`] >>
  gvs[eval_operand_def, mload_def, mem_word_at_def]
QED
