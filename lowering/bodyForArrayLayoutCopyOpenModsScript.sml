(* Openness at the actual Array For item-copy compiler cut. *)
Theory bodyForArrayLayoutCopyOpenMods
Ancestors
  bodyFullForArrayRound stmtLowering compileEnv copyExecution typedCopyDomain
  exprOpenPrimitives exprOpenCopies exprOpenTerminals venomInst

Theorem array_item_copy_open[local]:
  acyclic_struct_metadata c.ce_struct_fields /\ ~block_is_terminated sa /\
  compile_iter_elem_copy c src dst stride loc (is_slot_addressed loc) fty sty sa =
    ((),sb) ==> ~block_is_terminated sb
Proof
  strip_tac >>
  qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_iter_elem_copy_def] >>
  Cases_on `loc` >> simp[is_slot_addressed_def]
  >- (IF_CASES_TAC
      >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
          drule emit_void_terminated >> simp[is_terminator_def]) >>
      strip_tac >> irule compile_store_memory_open >>
      goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >> simp[])
  >- (simp[compile_slot_to_memory_shape, comp_ignore_bind_def, comp_bind_def,
           comp_return_def] >> strip_tac >> gvs[slot_copy_final_def, block_is_terminated_def])
  >- (simp[compile_slot_to_memory_shape, comp_ignore_bind_def, comp_bind_def,
           comp_return_def] >> strip_tac >> gvs[slot_copy_final_def, block_is_terminated_def])
  >- (IF_CASES_TAC
      >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
          drule emit_void_terminated >> simp[is_terminator_def]) >>
      strip_tac >> drule_all_then ACCEPT_TAC compile_imm_copy_to_memory_open) >>
  IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
      drule emit_void_terminated >> simp[is_terminator_def]) >>
  strip_tac >> drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem for_array_layout_copy_open_mods:
  for_nonslot_layout (c,id,fty,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa0,vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL)
    (bc,saD,saA,xd,capacity,aidItem)
    (entry,cond,bod,incr,exit,idx,invalid,valid,done_var,next_var)
    (sa,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy) body_cut /\
  acyclic_struct_metadata c.ce_struct_fields ==>
  ~block_is_terminated sbCopy
Proof
  PairCases_on `body_cut` >> strip_tac >>
  qhdtm_x_assum `for_nonslot_layout`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  `~block_is_terminated saCopy` by
    (qpat_assum `emit_op ADD _ _ = (_,saCopy)`
       (mp_then (Pat `emit_op _ _ _ = _`) irule emit_op_nonterminator_open) >>
     simp[is_terminator_def]) >>
  drule_all_then ACCEPT_TAC array_item_copy_open
QED
