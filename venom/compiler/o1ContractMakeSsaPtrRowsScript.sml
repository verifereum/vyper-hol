(*
 * The per-state rows of the pointer discipline (access_ok, taint_ok)
 * carry from an input state to the output state a frame lockstep pairs
 * it with, and MakeSSA adds no DALLOCA.
 *)
Theory o1ContractMakeSsaPtrRows
Ancestors
  o1FrameLockstep ptrDiscipline contextCodegenRel codegenRel
  makeSsaCurrentDefs makeSsaCurrentOrigin o1PassContract venomWf

Theorem lockstep_taint_operands[local]:
  inst_pair sg inst inst' /\ state_rel sg s s' /\
  ghost_rel sg G tn G' tn' /\ taint_ok fn tn inst s ==>
  !op. MEM op inst'.inst_operands /\ op_taint tn' op <> {} ==>
    inst'.inst_opcode = ASSIGN \/
    ((inst'.inst_opcode = SHL \/ inst'.inst_opcode = SHR \/
      inst'.inst_opcode = SAR) /\
     ?n. inst'.inst_operands = [n; op] /\ op_taint tn' n = {}) \/
    ((inst'.inst_opcode = MSTORE \/ inst'.inst_opcode = SSTORE \/
      inst'.inst_opcode = TSTORE \/ inst'.inst_opcode = ISTORE) /\
     ?a. inst'.inst_operands = [a; op] /\ op_taint tn' a = {})
Proof
  rpt strip_tac >>
  `vars_ghost_rel sg G tn.t_var G' tn'.t_var` by gvs[ghost_rel_def] >>
  drule_all inst_pair_ops_ghost >> strip_tac >>
  drule_all listTheory.LIST_REL_MEM_IMP_R >> strip_tac >>
  gvs[] >>
  qpat_x_assum `taint_ok _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [taint_ok_def]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[inst_pair_def, listTheory.LIST_REL_CONS1]
QED

Theorem lockstep_access_comparison[local]:
  inst_pair sg inst inst' /\ state_rel sg s s' /\
  ghost_rel sg G tn G' tn' /\ access_ok lo G fn inst s ==>
  !u w. (inst'.inst_opcode = LT \/ inst'.inst_opcode = GT \/
          inst'.inst_opcode = EQ) /\
    inst'.inst_operands = [Var u; Var w] /\
    (u IN FDOM G' \/ w IN FDOM G') ==>
    ?b sz x y. FLOOKUP G' u = SOME (b,sz) /\ FLOOKUP G' w = SOME (b,sz) /\
      0 < sz /\ eval_operand (Var u) s' = SOME x /\
      eval_operand (Var w) s' = SOME y /\
      b <= w2n x /\ w2n x <= b + sz /\ b <= w2n y /\ w2n y <= b + sz
Proof
  strip_tac >>
  `vars_ghost_rel sg G tn.t_var G' tn'.t_var` by gvs[ghost_rel_def] >>
  drule_all inst_pair_ops_ghost >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[inst_pair_def, listTheory.LIST_REL_CONS2, op_rename_def] >>
  rename1 `inst.inst_operands = [Var v; Var z]` >>
  `FLOOKUP G' u = FLOOKUP G v /\ FLOOKUP G' w = FLOOKUP G z` by
    metis_tac[vars_ghost_rel_def] >>
  `v IN FDOM G \/ z IN FDOM G` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  gvs[access_ok_def] >> metis_tac[]
QED

Theorem inst_pair_write_offset[local]:
  inst_pair sg inst inst' /\ mem_write_ops inst' = SOME ops' ==>
  ?ops. mem_write_ops inst = SOME ops /\
        op_rename sg ops.iao_ofst ops'.iao_ofst
Proof
  strip_tac >>
  gvs[inst_pair_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[memLocDefsTheory.mem_write_ops_def, AllCaseEqs(),
      listTheory.LIST_REL_CONS2]
QED

Theorem inst_pair_read_offset[local]:
  inst_pair sg inst inst' /\ mem_read_ops inst' = SOME ops' ==>
  ?ops. mem_read_ops inst = SOME ops /\
        op_rename sg ops.iao_ofst ops'.iao_ofst
Proof
  strip_tac >>
  gvs[inst_pair_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[memLocDefsTheory.mem_read_ops_def, AllCaseEqs(),
      listTheory.LIST_REL_CONS2] >>
  `LIST_REL (op_rename sg) (REVERSE inst.inst_operands)
     (REVERSE inst'.inst_operands)` by
    metis_tac[listTheory.LIST_REL_REVERSE] >>
  qpat_x_assum `LIST_REL _ (REVERSE _) _` mp_tac >>
  asm_rewrite_tac[] >>
  simp_tac pure_ss [listTheory.LIST_REL_CONS2] >>
  strip_tac >> gvs[]
QED

(* Paired states (p): same opcode, operands renamed by sg, equal values,
   provenance and taint through ghost_rel, equal memory ranges
   (write_ranges_pair, read_ranges_pair, inst_pair_ops_ghost); the
   revert exemptions carry by the two implications.  Unpaired states
   (~p) run an ASSIGN or an operand-free NOP: no memory range, no
   comparison, and taint_ok allows ASSIGN any operand. *)
Theorem lockstep_ptr_rows:
  lockstep_sim L C C' fn fn' pos R /\ R p (inst,s) sg (inst',s') /\
  ghost_rel sg G tn G' tn' /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  (p /\ in_revert_forward fn s ==> in_revert_forward fn' s') /\
  (p /\ about_to_revert fn inst s ==> about_to_revert fn' inst' s') /\
  (~p /\ inst'.inst_opcode = NOP ==> inst'.inst_operands = []) ==>
  access_ok lo G' fn' inst' s' /\ taint_ok fn' tn' inst' s'
Proof
  cheat
QED

(* make_ssa_current_fn_origin: a DALLOCA of the output is a renamed
   instruction of the input, with the same opcode. *)
Theorem make_ssa_current_fn_dalloca:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts fn') ==>
  EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts fn)
Proof
  cheat
QED
