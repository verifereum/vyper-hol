Theory lowerDloadPtrTerminal
Ancestors
  lowerDloadPtrForward lowerDloadPtrJointClosureProbe lowerDloadPtrJointNext
  lowerDloadPtrRel o1ContractLowerDload
  lowerDloadDefs venomInst list rich_list

(* Reverse prefix origin is independent of resolver equalities and freshness.
   Even malformed DLOAD branches cannot begin with ASSIGN or REVERT. *)
Theorem lower_dload_terminal_prefix_origin:
  !pre q xs rest q'.
    EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = REVERT) pre /\
    lower_dload_insts_supply q xs = (pre ++ rest,q') ==>
    ?tail. xs = pre ++ tail /\ lower_dload_insts_supply q tail = (rest,q')
Proof
  Induct_on `pre`
  >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `xs`
  >- gvs[lower_dload_insts_supply_def] >>
  rename1 `lower_dload_insts_supply q (i::is) = _` >>
  Cases_on `lower_dload_inst_supply q i` >>
  rename1 `lower_dload_inst_supply q i = (out,q1)` >>
  Cases_on `lower_dload_insts_supply q1 is` >>
  rename1 `lower_dload_insts_supply q1 is = (outs,q2)` >>
  `out <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  gvs[lower_dload_insts_supply_def] >>
  Cases_on `out` >- gvs[] >>
  gvs[] >>
  `h = i` by
    (irule lower_dload_inst_supply_control >>
     conj_tac >- (goal_assum $ drule_at Any >> simp[]) >>
     simp[is_terminator_def]) >>
  gvs[] >>
  rename1 `lower_dload_inst_supply q i = (i::t,q1)` >>
  `lower_dload_inst_supply q i = ([i],q)` by
    (irule lower_dload_inst_supply_special >> simp[] >> metis_tac[]) >>
  gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexists `tail` >> simp[]
QED

Theorem lower_dload_terminal_boundary_origin:
  lower_dload_insts_supply q (left ++ src) = (pre ++ mid ++ rest,q') /\
  lower_dload_insts_supply q left = (pre,u) /\
  EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = REVERT) mid ==>
  ?tail. src = mid ++ tail /\
    lower_dload_insts_supply u tail = (rest,q') /\
    (!k. k <= LENGTH mid ==>
      lower_dload_insts_supply q (TAKE (LENGTH left + k) (left ++ src)) =
        (pre ++ TAKE k mid,u))
Proof
  strip_tac >>
  drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
  drule_all lower_dload_terminal_prefix_origin >> strip_tac >>
  qexists `tail` >> simp[TAKE_APPEND] >> rpt strip_tac >>
  simp[TAKE_APPEND] >>
  `lower_dload_insts_supply u (TAKE k mid) = (TAKE k mid,u)` by
    (irule lower_dload_insts_supply_unchanged >>
     gvs[EVERY_MEM] >> rpt strip_tac >>
     `MEM q'' mid` by metis_tac[MEM_TAKE] >>
     qpat_x_assum `!i. MEM i mid ==> _` drule >> simp[]) >>
  Cases_on `lower_dload_insts_supply q (left ++ TAKE k mid)` >>
  drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
  `k - LENGTH mid = 0` by decide_tac >>
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem lower_dload_terminal_index_origin:
  lower_dload_insts_supply q xs = (pre ++ mid ++ rest,q') /\
  n <= LENGTH xs /\
  lower_dload_insts_supply q (TAKE n xs) = (pre,u) /\
  EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = REVERT) mid ==>
  n + LENGTH mid <= LENGTH xs /\
  TAKE (LENGTH mid) (DROP n xs) = mid /\
  (!k. k <= LENGTH mid ==>
    lower_dload_insts_supply q (TAKE (n+k) xs) = (pre ++ TAKE k mid,u))
Proof
  strip_tac >>
  `?tail. DROP n xs = mid ++ tail /\
    lower_dload_insts_supply u tail = (rest,q') /\
    (!k. k <= LENGTH mid ==>
      lower_dload_insts_supply q
        (TAKE (LENGTH (TAKE n xs) + k) (TAKE n xs ++ DROP n xs)) =
        (pre ++ TAKE k mid,u))` by
    (match_mp_tac lower_dload_terminal_boundary_origin >> simp[]) >>
  `LENGTH (DROP n xs) = LENGTH mid + LENGTH tail` by
    metis_tac[LENGTH_APPEND] >>
  gvs[TAKE_DROP, LENGTH_DROP, LENGTH_TAKE] >> simp[TAKE_APPEND]
QED

Theorem dload_control_terminal_slice_origin:
  dload_control_match q f g s t i emitted 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  lookup_block t.vs_current_bb g.fn_blocks = SOME tb /\
  d <= LENGTH (DROP t.vs_inst_idx tb.bb_instructions) /\
  mid = TAKE d (DROP t.vs_inst_idx tb.bb_instructions) /\
  EVERY (\j. j.inst_opcode = ASSIGN \/ j.inst_opcode = REVERT) mid ==>
  ?bb bs pre u.
    MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx + LENGTH mid <= LENGTH bb.bb_instructions /\
    TAKE (LENGTH mid) (DROP s.vs_inst_idx bb.bb_instructions) = mid /\
    t.vs_inst_idx = LENGTH pre /\
    lower_dload_insts_supply bs (TAKE s.vs_inst_idx bb.bb_instructions) = (pre,u) /\
    (!k. k < LENGTH mid ==>
      EL (s.vs_inst_idx+k) bb.bb_instructions =
      EL (t.vs_inst_idx+k) tb.bb_instructions) /\
    (!k. k <= LENGTH mid ==>
      lower_dload_insts_supply bs (TAKE (s.vs_inst_idx+k) bb.bb_instructions) =
        (pre ++ TAKE k mid,u))
Proof
  strip_tac >>
  qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_control_match_def] >> strip_tac >>
  `?aq. lower_dload_blocks_supply q f.fn_blocks = (g.fn_blocks,aq)` by
    (gvs[lower_dload_function_supply_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all dload_blocks_supply_el >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lower_dload_block_supply bs _ = (gb,_)` >>
  `gb.bb_label = (EL bi f.fn_blocks).bb_label /\
   ?aq. lower_dload_insts_supply bs (EL bi f.fn_blocks).bb_instructions =
     (gb.bb_instructions,aq)` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME gb` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[Abbr `gb`, EL_MEM]) >>
  gvs[] >>
  `?outs. gb.bb_instructions = before ++ outs` by
    (`lower_dload_insts_supply bs
        (TAKE s.vs_inst_idx (EL bi f.fn_blocks).bb_instructions ++
         DROP s.vs_inst_idx (EL bi f.fn_blocks).bb_instructions) =
       (gb.bb_instructions,aq')` by simp[] >>
     drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  gvs[DROP_APPEND] >>
  `lower_dload_insts_supply bs (EL bi f.fn_blocks).bb_instructions =
    (before ++ TAKE d outs ++ DROP d outs,aq')` by simp[TAKE_DROP] >>
  `s.vs_inst_idx <= LENGTH (EL bi f.fn_blocks).bb_instructions` by decide_tac >>
  drule_all lower_dload_terminal_index_origin >> strip_tac >>
  qexistsl [`EL bi f.fn_blocks`,`bs`,`before`,`is`] >>
  gvs[EL_MEM, LENGTH_TAKE, arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> simp[EL_APPEND_EQN] >>
  qpat_x_assum `TAKE d _ = TAKE d _` mp_tac >>
  qpat_x_assum `k < d` mp_tac >>
  qpat_x_assum `d + s.vs_inst_idx <= _` mp_tac >>
  qpat_x_assum `d <= LENGTH outs` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  `k < LENGTH outs /\ k + s.vs_inst_idx <
    LENGTH (EL bi f.fn_blocks).bb_instructions` by decide_tac >>
  metis_tac[EL_TAKE, EL_DROP, arithmeticTheory.ADD_COMM]
QED
