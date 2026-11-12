(* Source-justified counted header loads; the following GT/ISZERO/ASSERT
   control suffix is handled independently of the load location. *)
Theory bodyPtrBopInHeaderLoad
Ancestors bodyPtrBopInHeaderContents bodyPtrBopInElementLoad
  bodyPtrBopInSlotLoad bodyPtrBopInCodeLoad venomInst venomState
  venomExecSemantics fragGasPathPtr finite_map arithmetic

Theorem membership_memory_header_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [out]) /\
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var src /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  ~is_word_type aty /\ lookup_var src s = SOME bw ==>
  LENGTH vs <= cap /\
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out (n2w (LENGTH vs)) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >> drule_all membership_located_memory_header >> strip_tac >> simp[] >>
  drule_all membership_positioned_mload_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_slot_header_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [arr_op] [out]) /\
  storage_holds cx tr (ArrayT ety (Dynamic cap)) tvv bw es s /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) ety = SOME tv ==>
  array_length (ArrayTV tv (Dynamic cap)) av <= cap /\
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out (n2w (array_length (ArrayTV tv (Dynamic cap)) av)) s
        with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >>
  `eval_operand p.ptr_operand s = SOME bw` by simp[eval_operand_def] >>
  drule_all membership_located_slot_header >> strip_tac >> simp[] >>
  `op_taint tn arr_op = {}` by fs[bodyPtrDefsTheory.ptr_vv_ok_def] >>
  drule_all membership_positioned_slot_load_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_code_header_path:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id DLOAD [arr_op] [out]) /\
  stmt_state_rel ctx fn cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT ety (Dynamic cap)) (Value (ArrayV av)) bw es s /\
  evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
  eval_operand arr_op s = SOME bw /\ op_taint tn arr_op = {} ==>
  array_length (ArrayTV tv (Dynamic cap)) av <= cap /\
  ?G'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G'
      (tn with t_var := tn.t_var |+ (out,{}))
      (OK (update_var out (n2w (array_length (ArrayTV tv (Dynamic cap)) av)) s
        with vs_inst_idx := SUC s.vs_inst_idx)) /\
    FLOOKUP G' out = NONE /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x)
Proof
  strip_tac >> drule_all membership_dynamic_code_header >> strip_tac >> simp[] >>
  drule_all (SRULE [] (GEN_ALL membership_positioned_dload_path)) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED
