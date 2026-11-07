(* The existing state_insts is the chronological log. It is used here only
   for allocation ages, never for adjacency across block boundaries. *)
Theory bodyPtrBytestringBuiltinsAllocationOrigins
Ancestors
  loweringShapeDefs emitHelper compileEnv arithmetic list venomInst

(* This interval interface records allocation origins without constraining
   mutable ASSIGN targets or forgetting the fragment's original counter. *)
Definition alloca_output_interval_def:
  alloca_output_interval (lo:num) (hi:num) code <=>
    !i x. MEM i code /\ i.inst_opcode = ALLOCA /\
          MEM x i.inst_outputs ==>
          ?k. x = STRING #"%" (toString k) /\ lo <= k /\ k < hi
End

Theorem state_insts_emit:
  emit i sa = (u,sb) ==> state_insts sb = state_insts sa ++ [i]
Proof
  simp[emit_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def, FLAT_APPEND, APPEND_ASSOC]
QED

Theorem state_insts_new_block:
  new_block lbl sa = (u,sb) ==> state_insts sb = state_insts sa
Proof
  simp[new_block_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def, FLAT_APPEND, APPEND_ASSOC]
QED

Theorem alloca_output_interval_nil[simp]:
  alloca_output_interval lo hi []
Proof
  simp[alloca_output_interval_def]
QED

Theorem alloca_output_interval_widen:
  lo' <= lo /\ hi <= hi' /\ alloca_output_interval lo hi code ==>
  alloca_output_interval lo' hi' code
Proof
  rw[alloca_output_interval_def] >>
  first_x_assum drule_all >> strip_tac >> qexists_tac `k` >>
  simp[] >> decide_tac
QED

Theorem alloca_output_interval_append:
  lo <= mid /\ mid <= hi /\
  alloca_output_interval lo mid xs /\
  alloca_output_interval mid hi ys ==>
  alloca_output_interval lo hi (xs ++ ys)
Proof
  rw[alloca_output_interval_def, MEM_APPEND] >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem emit_op_alloca_origin:
  emit_op ALLOCA args sa = (op,sb) ==>
  ?i. state_insts sb = state_insts sa ++ [i] /\
      i = mk_inst sa.cs_next_id ALLOCA args [STRING #"%" (toString sa.cs_next_var)] /\
      op = Var (STRING #"%" (toString sa.cs_next_var)) /\
      sb.cs_next_var = sa.cs_next_var + 1 /\
      alloca_output_interval sa.cs_next_var sb.cs_next_var [i]
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def, FLAT_APPEND, APPEND_ASSOC,
      alloca_output_interval_def, mk_inst_def]
QED

Theorem raw_emit_alloca_origin:
  emit i sa = (u,sb) /\
  (i.inst_opcode = ALLOCA ==>
    !x. MEM x i.inst_outputs ==>
        ?k. x = STRING #"%" (toString k) /\ lo <= k /\ k < hi) ==>
  state_insts sb = state_insts sa ++ [i] /\
  alloca_output_interval lo hi [i]
Proof
  rpt strip_tac
  >- metis_tac[state_insts_emit] >>
  gvs[alloca_output_interval_def]
QED

Theorem state_insts_fresh_var:
  fresh_var sa = (x,sb) ==>
  state_insts sb = state_insts sa /\ sb.cs_next_var = sa.cs_next_var + 1
Proof
  simp[fresh_var_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def]
QED

Theorem state_insts_fresh_id:
  fresh_id sa = (x,sb) ==>
  state_insts sb = state_insts sa /\ sb.cs_next_var = sa.cs_next_var
Proof
  simp[fresh_id_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def]
QED

Theorem state_insts_fresh_label:
  fresh_label prefix sa = (x,sb) ==>
  state_insts sb = state_insts sa /\ sb.cs_next_var = sa.cs_next_var
Proof
  simp[fresh_label_def] >> strip_tac >>
  gvs[state_insts_def, all_blocks_def]
QED
