Theory extcallReturnCompileRelabel
Ancestors
  exprSimAbiGasBridge emitHelper fragExec compileEnv list rich_list venomInst

Definition return_compile_transport_def:
  return_compile_transport sa L ids (m : compile_state -> 'a # compile_state) <=>
    !u x v. cs_extends sa u /\ m u = (x,v) ==>
      cs_extends sa v /\
      m (start_swap sa L ids u) = (x,start_swap sa L ids v)
End

Theorem return_start_swap_initial:
  start_swap sa L ids sa = start_relabel L ids sa
Proof
  simp[start_swap_def, emitted_blocks_def, start_relabel_def]
QED

Theorem return_start_swap_append:
  u.cs_blocks = bs ++ sa.cs_blocks ==>
  start_swap sa L ids u =
    if bs = [] then
      u with <|cs_current_bb := L;
        cs_current_insts := MAP (\id. mk_inst id NOP [] []) ids ++
          DROP (LENGTH sa.cs_current_insts) u.cs_current_insts|>
    else
      u with cs_blocks := FRONT bs ++
        [LAST bs with <|bb_label := L;
          bb_instructions := MAP (\id. mk_inst id NOP [] []) ids ++
            DROP (LENGTH sa.cs_current_insts) (LAST bs).bb_instructions|>] ++
        sa.cs_blocks
Proof
  strip_tac >> drule emitted_blocks_append >> strip_tac >>
  simp[start_swap_def, NULL_EQ, DROP_LENGTH_APPEND]
QED

Theorem return_compile_transport_return:
  return_compile_transport sa L ids (comp_return x)
Proof
  simp[return_compile_transport_def, comp_return_def]
QED

Theorem return_compile_transport_bind:
  return_compile_transport sa L ids m /\
  (!x. return_compile_transport sa L ids (f x)) ==>
  return_compile_transport sa L ids (comp_bind m f)
Proof
  simp[return_compile_transport_def, comp_bind_def] >> rpt strip_tac >>
  Cases_on `m u` >> gvs[] >>
  first_x_assum (drule_at Any) >> simp[] >> strip_tac >>
  first_x_assum (drule_at Any) >> simp[]
QED

Theorem return_compile_transport_ignore_bind:
  return_compile_transport sa L ids m /\
  return_compile_transport sa L ids n ==>
  return_compile_transport sa L ids (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def] >>
  simp[return_compile_transport_bind]
QED

Theorem return_compile_transport_fresh_var:
  return_compile_transport sa L ids fresh_var
Proof
  rw[return_compile_transport_def, fresh_var_def] >>
  fs[cs_extends_def] >>
  `emitted_blocks sa u = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new = []` >>
  simp[start_swap_def, emitted_blocks_def, NULL_EQ, cs_extends_def,
       TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

Theorem return_compile_transport_fresh_id:
  return_compile_transport sa L ids fresh_id
Proof
  rw[return_compile_transport_def, fresh_id_def] >>
  fs[cs_extends_def] >>
  `emitted_blocks sa u = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new = []` >>
  simp[start_swap_def, emitted_blocks_def, NULL_EQ, cs_extends_def,
       TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

Theorem return_compile_transport_fresh_label:
  return_compile_transport sa L ids (fresh_label suffix)
Proof
  rw[return_compile_transport_def, fresh_label_def] >>
  fs[cs_extends_def] >>
  `emitted_blocks sa u = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new = []` >>
  simp[start_swap_def, emitted_blocks_def, NULL_EQ, cs_extends_def,
       TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
QED

Theorem return_compile_transport_emit:
  return_compile_transport sa L ids (emit inst)
Proof
  rw[return_compile_transport_def, emit_def] >>
  `cs_extends sa (u with cs_current_insts := u.cs_current_insts ++ [inst])` by
    (irule cs_extends_trans >> qexists_tac `u` >>
     simp[cs_extends_same_block]) >>
  simp[] >>
  qpat_x_assum `cs_extends sa (u with cs_current_insts := _)` kall_tac >>
  fs[cs_extends_def] >>
  `emitted_blocks sa u = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new = []` >>
  simp[start_swap_def, emitted_blocks_def, NULL_EQ,
       TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  gvs[] >> imp_res_tac IS_PREFIX_LENGTH >> simp[DROP_APPEND1]
QED

Theorem return_compile_new_block_state:
  cs_extends sa u /\ new_block lbl u = (old,v) ==>
  cs_extends sa v /\
  ?old'. new_block lbl (start_swap sa L ids u) =
    (old',start_swap sa L ids v)
Proof
  rpt gen_tac >> strip_tac >> gvs[new_block_def] >>
  conj_tac >- (irule cs_extends_trans >> qexists_tac `u` >>
    simp[] >> irule cs_extends_new_block >> simp[new_block_def] >>
    qexists_tac `lbl` >> simp[]) >>
  fs[cs_extends_def] >>
  `emitted_blocks sa u = new` by
    (irule emitted_blocks_append >> simp[]) >>
  Cases_on `new = []` >>
  simp[start_swap_def, emitted_blocks_def, NULL_EQ,
       TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  `SUC (LENGTH new + LENGTH sa.cs_blocks) - (LENGTH sa.cs_blocks + 1) =
     LENGTH new` by decide_tac >>
  simp[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  Cases_on `new` >> gvs[]
QED

Theorem return_compile_transport_emit_op:
  return_compile_transport sa L ids (emit_op opc ops)
Proof
  simp[emit_op_def, return_compile_transport_bind,
       return_compile_transport_ignore_bind, return_compile_transport_return,
       return_compile_transport_fresh_id, return_compile_transport_fresh_var,
       return_compile_transport_emit]
QED

Theorem return_compile_transport_emit_void:
  return_compile_transport sa L ids (emit_void opc ops)
Proof
  simp[emit_void_def, return_compile_transport_bind,
       return_compile_transport_fresh_id, return_compile_transport_emit]
QED

Theorem return_compile_transport_emit_inst:
  return_compile_transport sa L ids (emit_inst opc ops outs)
Proof
  simp[emit_inst_def, return_compile_transport_bind,
       return_compile_transport_fresh_id, return_compile_transport_emit]
QED

Theorem return_compile_transport_new_block_ignore:
  return_compile_transport sa L ids m ==>
  return_compile_transport sa L ids (comp_ignore_bind (new_block lbl) m)
Proof
  simp[return_compile_transport_def, comp_ignore_bind_def, comp_bind_def] >>
  rpt strip_tac >> Cases_on `new_block lbl u` >> gvs[] >>
  drule_all return_compile_new_block_state >>
  disch_then (qspecl_then [`ids`,`L`] strip_assume_tac) >>
  simp[] >> first_x_assum (drule_at Any) >> simp[]
QED

Theorem return_compile_transport_oblivious:
  (!sa L ids. LENGTH ids = LENGTH sa.cs_current_insts ==>
    return_compile_transport sa L ids m) ==>
  frag_start_oblivious m
Proof
  rw[frag_start_oblivious_def] >>
  first_x_assum (qspecl_then [`sa`,`L`,`ids`] mp_tac) >>
  simp[return_compile_transport_def] >>
  disch_then (drule_at Any) >>
  simp[cs_extends_refl, return_start_swap_initial]
QED

Theorem return_compile_transport_emit_block_emit:
  return_compile_transport sa L ids
    (comp_ignore_bind (emit i)
      (comp_ignore_bind (new_block lbl) (emit j)))
Proof
  simp[return_compile_transport_ignore_bind, return_compile_transport_emit,
       return_compile_transport_new_block_ignore]
QED
