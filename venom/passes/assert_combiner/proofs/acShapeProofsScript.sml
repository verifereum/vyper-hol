(*
 * Assert Combiner — instruction-level shape of the transform
 *
 * Each original instruction becomes itself, or (only for an ASSERT) a NOP
 * or rewritten ASSERT with the same id, possibly preceded by the OR/ISZERO
 * pair for that assert. Used by the wf_function and ssa_form obligations.
 *)

Theory acShapeProofs
Ancestors
  acChainProofs venomInst assertCombinerDefs venomWf list

(* What ac_apply_merge_step emits for one original instruction. *)
Definition ac_out_shape_def:
  ac_out_shape id_base cands inst out <=>
    out = [inst] \/
    inst.inst_opcode = ASSERT /\
    ?inst'.
      inst'.inst_id = inst.inst_id /\
      (inst'.inst_opcode = NOP /\ inst'.inst_outputs = [] \/
       inst'.inst_opcode = ASSERT /\ inst'.inst_outputs = inst.inst_outputs) /\
      (out = [inst'] \/
       (?mc. MEM mc cands /\ mc.mc_second_id = inst.inst_id) /\
       ?o1 o2.
         out =
           [<| inst_id := ac_or_id id_base inst.inst_id; inst_opcode := OR;
               inst_operands := o1;
               inst_outputs := [ac_or_var inst.inst_id] |>;
            <| inst_id := ac_or_id id_base inst.inst_id + 1;
               inst_opcode := ISZERO; inst_operands := o2;
               inst_outputs := [ac_iz_var inst.inst_id] |>;
            inst'])
End

Triviality ac_FIND_SOME_P[local]:
  !P l x. FIND P l = SOME x ==> P x
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Theorem ac_step_shape:
  !id_base cands mp inst.
    (!mc. MEM mc cands /\
          (mc.mc_first_id = inst.inst_id \/ mc.mc_second_id = inst.inst_id) ==>
          inst.inst_opcode = ASSERT) ==>
    ac_out_shape id_base cands inst
      (SND (ac_apply_merge_step id_base cands (mp, []) inst))
Proof
  rpt strip_tac >>
  simp[ac_apply_merge_step_def, LET_THM] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac FIND_MEM >> imp_res_tac ac_FIND_SOME_P >>
  gvs[ac_out_shape_def, EXISTS_MEM] >>
  res_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_foldl_shape:
  !insts id_base cands mp.
    (!inst mc. MEM inst insts /\ MEM mc cands /\
       (mc.mc_first_id = inst.inst_id \/ mc.mc_second_id = inst.inst_id) ==>
       inst.inst_opcode = ASSERT) ==>
    ?outs. LIST_REL (ac_out_shape id_base cands) insts outs /\
           SND (FOLDL (ac_apply_merge_step id_base cands) (mp, []) insts) =
           FLAT outs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac
    (Q.INST [`id_base` |-> `id_base`] ac_foldl_cons) >>
  Cases_on `ac_apply_merge_step id_base cands (mp, []) h` >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`id_base`, `cands`, `q`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `r :: outs` >> simp[] >>
  qspecl_then [`id_base`, `cands`, `mp`, `h`] mp_tac ac_step_shape >>
  impl_tac >- metis_tac[] >> simp[]
QED

Triviality ac_mem_same_id[local]:
  !l x y. ALL_DISTINCT (MAP (\i. i.inst_id) l) /\ MEM x l /\ MEM y l /\
          x.inst_id = y.inst_id ==> x = y
Proof
  Induct >> simp[] >> rw[] >> gvs[MEM_MAP] >> metis_tac[]
QED

Theorem ac_transform_block_shape:
  !dfg id_base bb.
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
    ?outs.
      LIST_REL (ac_out_shape id_base
                  (ac_scan_block dfg bb.bb_instructions NONE))
               bb.bb_instructions outs /\
      (ac_transform_block dfg id_base bb).bb_instructions = FLAT outs
Proof
  rpt strip_tac >> simp[ac_transform_block_def, LET_THM] >>
  irule ac_foldl_shape >> rpt strip_tac
  >- (drule ac_scan_first_is_assert >> strip_tac >> gvs[] >>
      `inst' = inst` by metis_tac[ac_mem_same_id] >> gvs[])
  >- (drule ac_scan_second_is_assert >> strip_tac >> gvs[] >>
      `inst' = inst` by metis_tac[ac_mem_same_id] >> gvs[])
QED
