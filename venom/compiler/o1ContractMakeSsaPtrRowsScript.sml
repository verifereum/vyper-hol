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
  inst_pair sg inst inst' ==>
  OPTREL (\ops ops'. op_rename sg ops.iao_ofst ops'.iao_ofst)
    (mem_write_ops inst) (mem_write_ops inst')
Proof
  strip_tac >>
  gvs[inst_pair_def] >>
  Cases_on `inst.inst_opcode` >>
  simp[memLocDefsTheory.mem_write_ops_def] >>
  namedCases_on `inst.inst_operands` ["", "a xs"] >>
  gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `xs` ["", "b ys"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `ys` ["", "c zs"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `zs` ["", "d ts"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `ts` ["", "e us"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `us` ["", "f vs"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `vs` ["", "g ws"] >> gvs[listTheory.LIST_REL_CONS1] >>
  Cases_on `ws` >> gvs[listTheory.LIST_REL_CONS1]
QED

Theorem inst_pair_read_offset[local]:
  inst_pair sg inst inst' ==>
  OPTREL (\ops ops'. op_rename sg ops.iao_ofst ops'.iao_ofst)
    (mem_read_ops inst) (mem_read_ops inst')
Proof
  strip_tac >> gvs[inst_pair_def] >>
  Cases_on `inst.inst_opcode = LOG`
  >- (simp[memLocDefsTheory.mem_read_ops_def] >>
      qabbrev_tac `xs = REVERSE inst.inst_operands` >>
      qabbrev_tac `ys = REVERSE inst'.inst_operands` >>
      `LIST_REL (op_rename sg) xs ys` by
        metis_tac[listTheory.LIST_REL_REVERSE, markerTheory.Abbrev_def] >>
      qpat_x_assum `LIST_REL _ inst.inst_operands _` kall_tac >>
      qpat_x_assum `Abbrev (xs = _)` kall_tac >>
      qpat_x_assum `Abbrev (ys = _)` kall_tac >>
      namedCases_on `xs` ["", "a ts"] >>
      gvs[listTheory.LIST_REL_CONS1] >>
      namedCases_on `ts` ["", "b us"] >> gvs[listTheory.LIST_REL_CONS1] >>
      Cases_on `us` >> gvs[listTheory.LIST_REL_CONS1]) >>
  Cases_on `inst.inst_opcode` >>
  gvs[memLocDefsTheory.mem_read_ops_def] >>
  namedCases_on `inst.inst_operands` ["", "a xs"] >>
  gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `xs` ["", "b ys"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `ys` ["", "c zs"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `zs` ["", "d ts"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `ts` ["", "e us"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `us` ["", "f vs"] >> gvs[listTheory.LIST_REL_CONS1] >>
  namedCases_on `vs` ["", "g ws"] >> gvs[listTheory.LIST_REL_CONS1] >>
  Cases_on `ws` >> gvs[listTheory.LIST_REL_CONS1]
QED

Theorem renamed_access_bound[local]:
  vars_ghost_rel sg G tn.t_var G' tn'.t_var /\
  OPTREL (\ops ops'. op_rename sg ops.iao_ofst ops'.iao_ofst) a a' /\
  ((lo < len + off \/ ?ops. a = SOME ops /\ op_prov G ops.iao_ofst <> NONE) ==>
   ?ops v b sz. a = SOME ops /\ ops.iao_ofst = Var v /\
     FLOOKUP G v = SOME (b,sz) /\ b <= off /\ len + off <= b + sz) ==>
  (lo < len + off \/ ?ops. a' = SOME ops /\ op_prov G' ops.iao_ofst <> NONE) ==>
  ?ops v b sz. a' = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G' v = SOME (b,sz) /\ b <= off /\ len + off <= b + sz
Proof
  Cases_on `a` >> Cases_on `a'` >> simp[] >> strip_tac >>
  rename1 `op_rename sg ops.iao_ofst ops'.iao_ofst` >>
  `op_prov G' ops'.iao_ofst = op_prov G ops.iao_ofst` by
    metis_tac[op_rename_ghost] >>
  strip_tac >>
  qpat_x_assum `_ ==> ?v b sz. _` mp_tac >>
  simp[] >> strip_tac >>
  Cases_on `ops'.iao_ofst` >>
  gvs[op_rename_def, vars_ghost_rel_def] >> metis_tac[]
QED

Theorem paired_access_ok[local]:
  inst_pair sg inst inst' /\ state_rel sg s s' /\
  ghost_rel sg G tn G' tn' /\ access_ok lo G fn inst s /\
  (in_revert_forward fn s ==> in_revert_forward fn' s') ==>
  access_ok lo G' fn' inst' s'
Proof
  strip_tac >>
  `vars_ghost_rel sg G tn.t_var G' tn'.t_var` by gvs[ghost_rel_def] >>
  `inst'.inst_opcode = inst.inst_opcode` by gvs[inst_pair_def] >>
  drule_all inst_pair_ops >> strip_tac >>
  `s'.vs_call_entry_fmp = s.vs_call_entry_fmp` by
    metis_tac[state_rel_def, execution_frame_fields] >>
  drule_all write_ranges_pair >> strip_tac >>
  drule_all read_ranges_pair >> strip_tac >>
  drule inst_pair_write_offset >> strip_tac >>
  drule inst_pair_read_offset >> strip_tac >>
  pure_rewrite_tac [access_ok_def] >> conj_tac
  >- (strip_tac >>
      `~in_revert_forward fn s` by metis_tac[] >>
      qpat_x_assum `access_ok _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [access_ok_def]) >>
      gvs[] >> conj_tac >> rpt gen_tac >> strip_tac >>
      irule renamed_access_bound >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_then (drule_then (drule_then (drule_then ACCEPT_TAC)))
    lockstep_access_comparison
QED

Theorem paired_taint_ok[local]:
  inst_pair sg inst inst' /\ state_rel sg s s' /\
  ghost_rel sg G tn G' tn' /\ taint_ok fn tn inst s /\
  (about_to_revert fn inst s ==> about_to_revert fn' inst' s') ==>
  taint_ok fn' tn' inst' s'
Proof
  strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by gvs[inst_pair_def] >>
  drule_all inst_pair_ops >> strip_tac >>
  drule_all read_ranges_pair >> strip_tac >>
  drule_then (drule_then (drule_then (drule_then assume_tac)))
    lockstep_taint_operands >>
  `tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans` by gvs[ghost_rel_def] >>
  qpat_x_assum `taint_ok fn tn _ _`
    (strip_assume_tac o REWRITE_RULE [taint_ok_def]) >>
  rewrite_tac [taint_ok_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (strip_tac >> `~about_to_revert fn inst s` by metis_tac[] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem lockstep_sim_rows[local]:
  lockstep_sim L C C' fn fn' pos R /\ R p (inst,s) sg (inst',s') ==>
  state_rel sg s s' /\ (p ==> inst_pair sg inst inst') /\
  (~p ==> inst'.inst_opcode = ASSIGN \/
          (inst'.inst_opcode = NOP /\ inst'.inst_operands = []))
Proof
  simp[lockstep_sim_def] >> strip_tac >>
  first_x_assum drule >> metis_tac[]
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
  strip_tac >> drule_all lockstep_sim_rows >> strip_tac >>
  Cases_on `p` >> gvs[]
  >- (conj_tac
      >- (irule paired_access_ok >> metis_tac[]) >>
      irule paired_taint_ok >> metis_tac[]) >>
  gvs[access_ok_def, taint_ok_def, source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def]
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
  strip_tac >>
  drule_at (Pos last) make_ssa_current_fn_origin >>
  impl_tac >- (gvs[make_ssa_input_ok_def] >> metis_tac[]) >>
  strip_tac >> gvs[listTheory.EXISTS_MEM] >>
  first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED
