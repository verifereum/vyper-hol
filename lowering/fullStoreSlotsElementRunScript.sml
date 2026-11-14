(* Uniform recursive element loop assembly. *)
Theory fullStoreSlotsElementRun
Ancestors
  fullStoreSlotsElements fullStoreSlotsElementStep fullStoreSlotsElementLayout
  fullStoreSlotsUniformLoop fullStoreSlotsMemberFrame
  fragGasOriginPtr context emitHelper exprLoweringProps loweringStateRelDefs
  compileEnv venomState ptrDiscipline venomInst finite_map list arithmetic words
  stateFrame stmtLoweringMono typedMemoryCopy fragExec pair

Theorem store_slots_elements_header_frame:
  emit_op LT [Var cv;cnt] a = (Var x,b) /\
  emit_op ISZERO [Var x] b = (Var y,c) /\
  emit_inst JNZ [Var y;Label exit;Label blabel] [] c = ((),d) /\
  lookup_var cv s = SOME (n2w j) /\
  eval_operand cnt s = SOME (n2w n) /\ j <= n /\ n < dimword(:256) /\
  FLOOKUP G cv = NONE /\ op_prov G cnt = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn cnt = {} /\
  cv <> x /\ cv <> y /\ (!p. old p ==> p <> x /\ p <> y) /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    lookup_var cv u = SOME (n2w j) /\ FLOOKUP Gf cv = NONE /\
    op_taint tf (Var cv) = {} /\
    ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if j=n then exit else blabel) /\
    (!p. old p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all store_slots_elements_header_origin_ptr >> strip_tac >>
  qexistsl_tac [`jump_to (if j=n then exit else blabel)
      (update_var y (if j=n then 1w else 0w)
        (update_var x (if j<n then 1w else 0w) s))`,
    `DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})`,
    `tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{})`] >>
  simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT,op_taint_def,execution_frame_def] >>
  rpt strip_tac >> gvs[op_taint_def,lookup_var_def] >>
  `p <> x /\ p <> y` by metis_tac[] >> simp[]
QED
