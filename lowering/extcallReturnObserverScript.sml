(* Complete a cut observer's resource metadata without adding reachable code. *)
Theory extcallReturnObserver
Ancestors
  extcallReturnCountedCheck exprSimAbiGasBridge abiMalformedRecursiveInterface
  venomInst compileEnv exprLoweringProps fragExec list unitShapeDefs callLayoutDefs
  venomWf localPtrsProps dftPipelineInvar sorting fcgDefs relation
  abiEncoderObserver venomExecSemantics venomExecProofs venomInstProofs1
  intCallCallee

Definition return_observer_complete_def:
  return_observer_complete func obs keep =
    obs with fn_blocks := obs.fn_blocks ++
      [<|bb_label := keep;
         bb_instructions := FILTER
           (\i. i.inst_opcode = ALLOCA /\ ~MEM i (fn_insts obs))
           (fn_insts func)|>]
End

Theorem return_observer_complete_members:
  MEM i (fn_insts (return_observer_complete func obs keep)) <=>
  MEM i (fn_insts obs) \/
  i.inst_opcode = ALLOCA /\ MEM i (fn_insts func)
Proof
  simp[return_observer_complete_def, fn_insts_def,
    MEM_fn_insts_blocks_iff, MEM_APPEND, MEM_FILTER,
    RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> metis_tac[]
QED

Theorem return_observer_complete_allocas:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts (return_observer_complete func obs keep)) <=>
     MEM i (fn_insts func)))
Proof
  simp[return_observer_complete_members] >> metis_tac[]
QED

Theorem return_observer_complete_scratch:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  abi_malformed_scratch_sites st en (return_observer_complete func obs keep) =
  abi_malformed_scratch_sites st en func
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[abi_malformed_scratch_sites_def, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem return_observer_complete_destination:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (abi_malformed_destination (return_observer_complete func obs keep)
      cenv scopes aid d n s <=>
   abi_malformed_destination func cenv scopes aid d n s)
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[abi_malformed_destination_def] >> metis_tac[]
QED

Theorem return_observer_complete_local_backed:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (local_backed (return_observer_complete func obs keep) p s b n <=>
   local_backed func p s b n)
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[local_backed_def] >> metis_tac[]
QED

Theorem return_observer_complete_local_ptrs:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (local_ptrs_rel (return_observer_complete func obs keep) cenv scopes s <=>
   local_ptrs_rel func cenv scopes s)
Proof
  strip_tac >> simp[local_ptrs_rel_def] >>
  metis_tac[return_observer_complete_local_backed]
QED

Theorem return_observer_complete_state_rel:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (state_rel (return_observer_complete func obs keep) cenv cx es s <=>
   state_rel func cenv cx es s)
Proof
  strip_tac >> drule return_observer_complete_local_ptrs >>
  simp[state_rel_def]
QED

Theorem return_observer_complete_immutable_sep:
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  (immutable_alloca_sep (return_observer_complete func obs keep) cenv cx es s <=>
   immutable_alloca_sep func cenv cx es s)
Proof
  strip_tac >> drule return_observer_complete_allocas >>
  simp[immutable_alloca_sep_def] >> metis_tac[]
QED

Theorem return_observer_complete_lookup:
  lookup_block lbl obs.fn_blocks = SOME bb ==>
  lookup_block lbl (return_observer_complete func obs keep).fn_blocks = SOME bb
Proof
  simp[return_observer_complete_def, lookup_block_def, FIND_APPEND_CASE]
QED

Theorem return_observer_complete_has_code:
  fn_has_code st en obs ==>
  fn_has_code st en (return_observer_complete func obs keep)
Proof
  rw[fn_has_code_def] >> metis_tac[return_observer_complete_lookup]
QED

Theorem return_observer_complete_fresh_label:
  ?keep. ~MEM keep (MAP (\bb. bb.bb_label) obs.fn_blocks) /\
    EVERY (\i. ~MEM (Label keep) i.inst_operands) (fn_insts obs)
Proof
  qspec_then `MAP (\bb. bb.bb_label) obs.fn_blocks ++
    FLAT (MAP (\i. MAP (\op. case op of Label l => l | _ => "")
      i.inst_operands) (fn_insts obs))` mp_tac frag_fresh_label >>
  simp[MEM_FLAT, MEM_MAP, EVERY_MEM] >> strip_tac >>
  qexists_tac `L` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!l. _` (qspec_then
    `MAP (\op. case op of Label l => l | _ => "") i.inst_operands` mp_tac) >>
  simp[MEM_MAP] >> conj_tac
  >- (qexists_tac `i` >> simp[]) >>
  qexists_tac `Label L` >> simp[]
QED

Theorem return_observer_complete_ids:
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i j. MEM i (fn_insts func) /\ MEM j (fn_insts obs) /\
         i.inst_id = j.inst_id ==> i = j) ==>
  fn_inst_ids_distinct (return_observer_complete func obs keep)
Proof
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
      FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
    fs[fn_inst_ids_distinct_def, fn_insts_def] >>
  simp[fn_inst_ids_distinct_def, return_observer_complete_def,
    MAP_APPEND, ALL_DISTINCT_APPEND] >> conj_tac
  >- fs[fn_inst_ids_distinct_def] >> conj_tac
  >- (irule all_distinct_map_filter >> simp[]) >>
  qpat_assum `!bbs. MAP _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[MEM_MAP, MEM_FILTER, GSYM fn_insts_def] >> metis_tac[]
QED

Theorem return_observer_allocas_permutation:
  ALL_DISTINCT (fn_insts func) /\ ALL_DISTINCT (fn_insts obs) /\
  (!i. i.inst_opcode = ALLOCA ==>
       (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) ==>
  PERM (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs))
       (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func))
Proof
  strip_tac >> irule sortingTheory.PERM_ALL_DISTINCT >>
  conj_tac
  >- (simp[MEM_FILTER] >> metis_tac[]) >>
  conj_tac >> irule listTheory.FILTER_ALL_DISTINCT >> simp[]
QED

Theorem return_observer_pending_charge:
  PERM (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs))
       (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)) ==>
  pending_alloca_size obs s = pending_alloca_size func s
Proof
  strip_tac >> simp[pending_alloca_size_def] >>
  `!code. FILTER (\i. i.inst_opcode = ALLOCA /\
                      i.inst_id NOTIN FDOM s.vs_allocas) code =
          FILTER (\i. i.inst_id NOTIN FDOM s.vs_allocas)
            (FILTER (\i. i.inst_opcode = ALLOCA) code)` by
    (Induct >> simp[] >> gen_tac >>
     Cases_on `h.inst_opcode = ALLOCA` >> simp[]) >>
  asm_rewrite_tac[] >> irule PERM_SUM >>
  irule PERM_MAP >> irule PERM_FILTER >> simp[]
QED

Definition return_observer_context_def:
  return_observer_context ctx obs = ctx with ctx_functions := [obs]
End

Theorem return_observer_context_calls:
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) ==>
  !a b. ~fn_directly_calls (return_observer_context ctx obs) a b
Proof
  simp[fn_directly_calls_def, return_observer_context_def,
       lookup_function_def, FIND_thm] >> metis_tac[]
QED

Theorem return_observer_context_reachable:
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) ==>
  !a b. ~TC (fn_directly_calls (return_observer_context ctx obs)) a b
Proof
  strip_tac >> drule return_observer_context_calls >> strip_tac >>
  simp[Once relationTheory.TC_CASES1]
QED

Theorem return_observer_context_alloca_room:
  alloca_room ctx func s /\
  pending_alloca_size obs s = pending_alloca_size func s /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) ==>
  alloca_room (return_observer_context ctx obs) obs s
Proof
  strip_tac >> drule return_observer_context_reachable >> strip_tac >>
  fs[alloca_room_def] >>
  simp[return_observer_context_def, lookup_function_def, FIND_thm] >>
  decide_tac
QED

Theorem return_observer_context_fmp_room:
  (!i. MEM i (fn_insts obs) ==>
       i.inst_opcode <> INVOKE /\ i.inst_opcode <> DALLOCA) ==>
  fmp_room (return_observer_context ctx obs) obs s
Proof
  strip_tac >>
  `!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE` by metis_tac[] >>
  drule return_observer_context_reachable >> strip_tac >>
  simp[fmp_room_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem return_observer_complete_no_dynamic:
  (!i. MEM i (fn_insts obs) ==>
       i.inst_opcode <> INVOKE /\ i.inst_opcode <> DALLOCA) ==>
  !i. MEM i (fn_insts (return_observer_complete func obs keep)) ==>
       i.inst_opcode <> INVOKE /\ i.inst_opcode <> DALLOCA
Proof
  rw[return_observer_complete_members] >> fs[]
QED

Theorem return_observer_complete_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) /\
  PERM (FILTER (\i. i.inst_opcode = ALLOCA)
         (fn_insts (return_observer_complete func obs keep)))
       (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==>
       i.inst_opcode <> INVOKE /\ i.inst_opcode <> DALLOCA) ==>
  stmt_state_rel
    (return_observer_context ctx (return_observer_complete func obs keep))
    (return_observer_complete func obs keep) cenv cx es s
Proof
  strip_tac >>
  drule return_observer_complete_no_dynamic >> strip_tac >>
  `pending_alloca_size (return_observer_complete func obs keep) s =
   pending_alloca_size func s` by
    (irule return_observer_pending_charge >> simp[]) >>
  fs[stmt_state_rel_def] >> rpt conj_tac
  >- (irule (iffRL return_observer_complete_state_rel) >> simp[])
  >- (irule return_observer_context_alloca_room >> metis_tac[])
  >- (irule return_observer_context_fmp_room >> metis_tac[])
  >- (irule (iffRL return_observer_complete_immutable_sep) >> simp[]) >>
  rpt strip_tac >>
  `MEM inst (fn_insts func)` by
    (fs[return_observer_complete_members] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem return_observer_step_context:
  abi_observer_step ctx fn cut s t <=> abi_observer_step ctx' fn cut s t
Proof
  simp[abi_observer_step_def, SF CONJ_ss, step_inst_non_invoke]
QED

Theorem return_observer_prefix_context:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  !ctx'. local_prefix ctx' fn cut s t
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 local_prefix_rules) >> simp[]) >>
  rpt strip_tac >>
  rename1 `abi_observer_step ctx fn cut s middle` >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle` >> metis_tac[return_observer_step_context]
QED

Theorem return_observer_complete_step:
  ~MEM keep (MAP (\bb. bb.bb_label) obs.fn_blocks) /\
  abi_observer_step ctx (return_observer_complete func obs keep) cut s t /\
  s.vs_current_bb <> keep /\ t.vs_current_bb <> keep ==>
  abi_observer_step ctx obs cut s t
Proof
  simp[abi_observer_step_def, return_observer_complete_def,
       lookup_block_def, FIND_APPEND_CASE, FIND_thm] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[eval_phis_preserves_current_bb]
QED

Theorem return_observer_terminator_jump[local]:
  step_inst 0 ctx inst s = OK middle /\ ~middle.vs_halted /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem return_observer_complete_lookup_off_keep:
  lbl <> keep ==>
  lookup_block lbl (return_observer_complete func obs keep).fn_blocks =
  lookup_block lbl obs.fn_blocks
Proof
  simp[return_observer_complete_def, lookup_block_def,
       FIND_APPEND_CASE, FIND_thm] >>
  Cases_on `FIND (\bb. bb.bb_label = lbl) obs.fn_blocks` >> simp[]
QED

Theorem return_observer_instruction_member:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  MEM inst (fn_insts fn)
Proof
  strip_tac >> drule lookup_block_MEM >> strip_tac >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  qexists_tac `bb` >> simp[] >>
  qpat_x_assum `get_instruction _ _ = _` mp_tac >>
  simp[get_instruction_def, AllCaseEqs(), MEM_EL] >> metis_tac[]
QED

Theorem return_observer_complete_avoids_keep:
  EVERY (\i. ~MEM (Label keep) i.inst_operands) (fn_insts obs) /\
  abi_observer_step ctx (return_observer_complete func obs keep) cut s t /\
  s.vs_current_bb <> keep ==>
  t.vs_current_bb <> keep
Proof
  strip_tac >> fs[abi_observer_step_def]
  >- (drule_all step_inst_non_invoke >> strip_tac >>
      metis_tac[step_inst_base_preserves_all]) >>
  drule_all return_observer_terminator_jump >> strip_tac >>
  `MEM inst (fn_insts obs)` by
    (`lookup_block s.vs_current_bb obs.fn_blocks = SOME bb` by
       metis_tac[return_observer_complete_lookup_off_keep] >>
     metis_tac[return_observer_instruction_member]) >>
  `~MEM (Label keep) inst.inst_operands` by fs[EVERY_MEM] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule_all frag_observer_jump_no_reentry >> simp[]
QED

Theorem return_observer_complete_prefix:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  !func obs keep ctx'. fn = return_observer_complete func obs keep /\
    ~MEM keep (MAP (\bb. bb.bb_label) obs.fn_blocks) /\
    EVERY (\i. ~MEM (Label keep) i.inst_operands) (fn_insts obs) /\
    s.vs_current_bb <> keep ==>
    local_prefix ctx' obs cut s t
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 local_prefix_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `abi_observer_step ctx (return_observer_complete func obs keep) cut s middle` >>
  `middle.vs_current_bb <> keep` by
    (irule return_observer_complete_avoids_keep >> metis_tac[]) >>
  irule (cj 2 local_prefix_rules) >> qexists_tac `middle` >> conj_tac
  >- (irule (iffLR return_observer_step_context) >>
      metis_tac[return_observer_complete_step]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem return_observer_step_static_charge:
  abi_observer_step ctx fn cut s t ==>
  t.vs_alloca_next + pending_alloca_size fn t <=
  s.vs_alloca_next + pending_alloca_size fn s
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  `MEM inst (fn_insts fn)` by
    metis_tac[return_observer_instruction_member] >>
  `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule_all step_inst_base_static_charge >>
  simp[pending_alloca_size_def] >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem return_observer_prefix_static_charge:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  t.vs_alloca_next + pending_alloca_size fn t <=
  s.vs_alloca_next + pending_alloca_size fn s
Proof
  ho_match_mp_tac local_prefix_ind >> simp[] >> rpt strip_tac >>
  drule return_observer_step_static_charge >> decide_tac
QED

Theorem return_observer_prefix_alloca_room:
  local_prefix ctx fn cut s t /\ alloca_room ctx fn s ==>
  alloca_room ctx fn t
Proof
  strip_tac >> drule return_observer_prefix_static_charge >>
  fs[alloca_room_def] >> decide_tac
QED

Theorem return_observer_prefix_fmp_room:
  local_prefix ctx fn cut s t /\ fmp_room ctx fn s /\
  t.vs_fmp = s.vs_fmp ==>
  fmp_room ctx fn t
Proof
  strip_tac >> irule fmp_room_static_charge >>
  qexists_tac `s` >> simp[] >>
  irule return_observer_prefix_static_charge >> metis_tac[]
QED
