(* Physical flat-copy payload for a prepared external return default. *)
Theory bodyExtReturnDefaultFlatMods
Ancestors
  bodyFullExtCallDefaultCopy bodyPtrDefs fragGasOriginPtr typedMemoryCopy
  context codegenRel ptrDiscipline venomState venomInst valueEncodingDefs
  vyperContext finite_map words

Theorem extcall_default_flat_payload:
  compile_store_memory cenv default_op (Var q) ret_type ret_type ds = ((),de) /\
  ~is_word_type ret_type /\ ~is_bytestring_type ret_type /\
  evaluate_type (get_tenv cx) ret_type = SOME rtv /\
  val_wf rtv dv /\ type_memory_bytes cenv ret_type = type_memory_size rtv /\
  (!x. default_op = Var x ==> not_fresh_at ds x) /\ not_fresh_at ds q /\
  eval_operand default_op u = SOME w /\ lookup_var q u = SOME dw /\
  ptr_mem_ok cx ret_type dv default_op Gu tu u /\
  (type_memory_size rtv <> 0 ==>
     (?x. default_op = Var x /\ ptr_covers Gu tu x u (type_memory_size rtv)) /\
     ptr_covers Gu tu q u (type_memory_size rtv) /\
     w2n w + type_memory_size rtv <= u.vs_alloca_next /\
     w2n dw + type_memory_size rtv <= u.vs_alloca_next /\
     u.vs_alloca_next < dimword (:256)) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  fn_has_code ds de func /\ ~u.vs_halted /\
  u.vs_current_bb = ds.cs_current_bb /\
  u.vs_inst_idx = LENGTH ds.cs_current_insts ==>
  ?p Gp tp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK p,Gp,tp)) /\
    typed_copy_state_frame ds (w2n dw) (type_memory_size rtv) u p /\
    (!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==>
      val_in_memory rtv dv (w2n dw) mem) /\
    (!x. not_fresh_at ds x ==>
      FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tp (Var x) = op_taint tu (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size rtv) ==>
      (i IN tp.t_mem <=> i IN tu.t_mem)) /\
    tp.t_stor = tu.t_stor /\ tp.t_trans = tu.t_trans /\ tp.t_imm = tu.t_imm /\
    ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
    p.vs_inst_idx = LENGTH de.cs_current_insts
Proof
  strip_tac >> drule_all extcall_default_copy_capacity_joint >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choosel_then [`p`,`Gp`,`tp`] strip_assume_tac)) >>
  qexistsl_tac [`p`,`Gp`,`tp`] >> simp[] >>
  metis_tac[]
QED
