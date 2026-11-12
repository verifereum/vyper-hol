Theory exprSimAbiEncodeObliviousCode
Ancestors
  exprSimAbiEncodeObliviousContext exprSimAbiGasBridge compileEnv fragExec
  exprLoweringProps list rich_list sorting emitHelper venomInst context

Theorem entry_shape_extends:
  !a b. entry_shape a b ==> cs_extends a b
Proof
  rw[entry_shape_def, cs_extends_def]
  >- (qexists_tac `[]` >> simp[])
  >> qexists_tac `front ++
       [<| bb_label := a.cs_current_bb;
           bb_instructions := a.cs_current_insts ++ tail |>]`
  >> simp[LAST_APPEND]
QED

Theorem frag_code_open:
  !a b tail. b.cs_blocks = a.cs_blocks /\
    b.cs_current_insts = a.cs_current_insts ++ tail ==>
    frag_code a b = tail
Proof
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def, DROP_APPEND]
QED

Theorem frag_code_closed:
  !a b front tail.
    b.cs_blocks = front ++
      [<| bb_label := a.cs_current_bb;
          bb_instructions := a.cs_current_insts ++ tail |>] ++ a.cs_blocks ==>
    frag_code a b = tail ++ FLAT (MAP (\bb. bb.bb_instructions) front) ++
      b.cs_current_insts
Proof
  rpt strip_tac
  >> simp[frag_code_def, emitted_blocks_def, TAKE_APPEND, DROP_APPEND,
          TAKE_LENGTH_TOO_LONG, FRONT_APPEND, LAST_APPEND]
QED

Theorem entry_shape_trans:
  !a b c. entry_shape a b /\ entry_shape b c ==> entry_shape a c
Proof
  rw[entry_shape_def]
  >- (disj1_tac >> simp[] >> metis_tac[APPEND_ASSOC])
  >- (disj2_tac >> qexistsl_tac [`front`, `tail ++ tail'`]
      >> simp[APPEND_ASSOC])
  >- (disj2_tac >> metis_tac[])
  >> disj2_tac
  >> qexistsl_tac [`front' ++
       [<| bb_label := b.cs_current_bb;
           bb_instructions := b.cs_current_insts ++ tail' |>] ++ front`, `tail`]
  >> simp[APPEND_ASSOC]
QED

Theorem frag_code_compose_perm:
  !a b c. entry_shape a b /\ entry_shape b c ==>
    PERM (frag_code a c) (frag_code a b ++ frag_code b c)
Proof
  rw[entry_shape_def]
  >> simp[frag_code_def, emitted_blocks_def, emitted_insts_def,
          TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG,
          FRONT_APPEND, LAST_APPEND, APPEND_ASSOC]
  >- (`LENGTH a.cs_current_insts -
         (LENGTH tail + LENGTH a.cs_current_insts) = 0` by decide_tac
      >> simp[DROP_LENGTH_TOO_LONG])
  >- (`LENGTH a.cs_current_insts -
         (LENGTH tail + LENGTH a.cs_current_insts) = 0` by decide_tac
      >> simp[DROP_LENGTH_TOO_LONG])
  >> `LENGTH front' + 1 - (LENGTH front + (LENGTH front' + 1)) = 0`
       by decide_tac
  >> `LENGTH front' + 1 - (LENGTH front + (LENGTH front' + 2)) = 0`
       by decide_tac
  >> simp[LAST_APPEND, FRONT_APPEND, DROP_APPEND, APPEND_ASSOC]
  >> simp[PERM_APPEND_IFF]
  >> metis_tac[PERM_APPEND, PERM_APPEND_IFF, PERM_REFL, PERM_TRANS,
               APPEND_ASSOC]
QED

Definition code_step_def:
  code_step P a b <=>
    entry_shape a b /\ a.cs_next_id <= b.cs_next_id /\
    EVERY (\i. a.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id)
      (frag_code a b) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code a b)) /\
    EVERY (\i. P i.inst_opcode) (frag_code a b)
End

Definition code_action_def:
  code_action P m <=> !a x b. m a = (x,b) ==> code_step P a b
End

Theorem code_step_refl:
  !P a. code_step P a a
Proof
  simp[code_step_def, entry_shape_refl, frag_code_def,
       emitted_blocks_def, emitted_insts_def]
QED

Theorem code_step_trans:
  !P a b c. code_step P a b /\ code_step P b c ==> code_step P a c
Proof
  rw[code_step_def]
  >- metis_tac[entry_shape_trans]
  >- (drule_all frag_code_compose_perm >> strip_tac
      >> drule PERM_EVERY >> disch_then (irule o iffRL)
      >> simp[EVERY_APPEND, EVERY_MEM] >> rpt strip_tac
      >> gvs[EVERY_MEM] >> res_tac >> decide_tac)
  >- (drule_all frag_code_compose_perm >> strip_tac
      >> `PERM (MAP (\i. i.inst_id) (frag_code a c))
               (MAP (\i. i.inst_id) (frag_code a b ++ frag_code b c))`
           by metis_tac[PERM_MAP]
      >> `ALL_DISTINCT (MAP (\i. i.inst_id)
                            (frag_code a b ++ frag_code b c))`
           suffices_by metis_tac[ALL_DISTINCT_PERM]
      >> simp[MAP_APPEND, ALL_DISTINCT_APPEND]
      >> gvs[EVERY_MEM, MEM_MAP] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS, prim_recTheory.LESS_REFL])
  >> drule_all frag_code_compose_perm >> strip_tac
  >> drule PERM_EVERY >> disch_then (irule o iffRL)
  >> simp[EVERY_APPEND]
QED

Theorem code_action_return:
  !P x. code_action P (comp_return x)
Proof
  simp[code_action_def, comp_return_def, code_step_refl]
QED

Theorem code_action_bind:
  !P m f. code_action P m /\ (!x. code_action P (f x)) ==>
    code_action P (comp_bind m f)
Proof
  rw[code_action_def, comp_bind_def]
  >> Cases_on `m a` >> gvs[]
  >> metis_tac[code_step_trans]
QED

Theorem code_action_ignore_bind:
  !P m n. code_action P m /\ code_action P n ==>
    code_action P (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def, code_action_bind]
QED

Theorem code_action_fresh_var:
  !P. code_action P fresh_var
Proof
  rw[code_action_def, fresh_var_def]
  >> simp[code_step_def, entry_shape_def, frag_code_def,
          emitted_blocks_def, emitted_insts_def]
QED

Theorem code_action_fresh_label:
  !P suffix. code_action P (fresh_label suffix)
Proof
  rw[code_action_def, fresh_label_def]
  >> simp[code_step_def, entry_shape_def, frag_code_def,
          emitted_blocks_def, emitted_insts_def]
QED

Theorem code_action_new_block:
  !P l. code_action P (new_block l)
Proof
  rw[code_action_def, new_block_def]
  >> simp[code_step_def, entry_shape_def, frag_code_def,
          emitted_blocks_def, emitted_insts_def]
  >> disj2_tac >> qexistsl_tac [`[]`, `[]`] >> simp[]
QED

Theorem code_action_emit_inst:
  !P opc ops outs. P opc ==> code_action P (emit_inst opc ops outs)
Proof
  rw[code_action_def, emit_inst_def, comp_bind_def, fresh_id_def,
     emit_def]
  >> simp[code_step_def, entry_shape_def, frag_code_def,
          emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
  >> qexists_tac `[mk_inst a.cs_next_id opc ops outs]` >> simp[mk_inst_def]
QED

Theorem code_action_emit_void:
  !P opc ops. P opc ==> code_action P (emit_void opc ops)
Proof
  simp[emit_void_def, GSYM emit_inst_def, code_action_emit_inst]
QED

Theorem code_action_emit_op:
  !P opc ops. P opc ==> code_action P (emit_op opc ops)
Proof
  rw[code_action_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_id_def, fresh_var_def, emit_def]
  >> simp[code_step_def, entry_shape_def, frag_code_def,
          emitted_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def]
  >> qexists_tac `[mk_inst a.cs_next_id opc ops
                       ["%" ++ toString a.cs_next_var]]`
  >> simp[mk_inst_def]
QED

Theorem code_action_alloc_buffer:
  !P size. P ALLOCA ==> code_action P (compile_alloc_buffer size)
Proof
  simp[compile_alloc_buffer_def, code_action_bind, code_action_emit_op,
       code_action_return]
QED

Theorem code_step_extends:
  !P a b. code_step P a b ==> cs_extends a b
Proof
  simp[code_step_def] >> metis_tac[entry_shape_extends]
QED

Theorem code_step_frag_facts:
  !a b.
    code_step (\opc. opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\
                      opc <> STOP /\ opc <> RETURN) a b ==>
    cs_extends a b /\ frag_ops_free a b /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code a b))
Proof
  rw[code_step_def, frag_ops_free_def] >> metis_tac[entry_shape_extends]
QED
