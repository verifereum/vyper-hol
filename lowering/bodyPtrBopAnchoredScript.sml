Theory bodyPtrBopAnchored
Ancestors bodyPtrBopScalarOutcome

(* The three outer anchors make compiler, ghost, and typing parameters
   inferable before matching the generic continuation conclusion. *)
Theorem bop_scalar_suffix_outcome_ptr_anchored:
  compile_binop bop x y ty bl el sa = (op,sb) ==>
  ghost_inv d cenv cx es G tn s ==>
  well_typed_binop ann bop t1 t2 ==>
  bop <> In /\ bop <> NotIn /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ((?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
   (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)) /\
  (!v t G' tn'. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v) /\
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      ghost_inv d cenv cx (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
      ghost_kept cenv es sa G tn s G' tn' ==>
      Q (INL v) (es with gas_obs := []) G' tn'
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (bop_result cx ann bop tys v1 v2 st,st)) (es,s,G,tn) Q
    (\res fin ghost r. expr_exit res r)
Proof
  ntac 3 strip_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_scalar_suffix_outcome_ptr >> simp[]
QED
