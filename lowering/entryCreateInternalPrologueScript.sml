(* The native trace through the callee's straight administrative code,
   at the fuel of the selected INVOKE. *)
Theory entryCreateInternalPrologue
Ancestors
  entryCreateInternalFocus entryCreateNativeResume entryCreateBodyCut fragExec exprLoweringProps
  dftGasFromListTraceDefs venomExecProofs venomInstProofs venomExecSemantics
  venomState venomInst venomRunBounded instIdxIndep list rich_list pair arithmetic

Theorem straight_create_trace[local]:
  !code s.
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code ==>
    ?pre. EVERY (\(_,_,i,_). MEM i code) pre /\
      create_trace_from p d k C f s = pre ++
        (case run_inst_seq code s of
           OK u => create_trace_from p d k C f
                     (u with vs_inst_idx := s.vs_inst_idx + LENGTH code)
         | _ => [])
Proof
  Induct >- (simp[run_inst_seq_def] >> metis_tac[APPEND_NIL]) >>
  rpt gen_tac >> strip_tac >> fs[EVERY_DEF] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >> fs[DROP_LENGTH_TOO_LONG]) >>
  `get_instruction bb s.vs_inst_idx = SOME h /\
   isPREFIX code (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    fs[DROP_CONS_EL, get_instruction_def] >>
  `step_inst k C h s = step_inst_base h s` by simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def]
  >- (rename1 `step_inst_base h s = OK u` >>
      `u.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
      drule_all create_trace_from_next >> strip_tac >>
      first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      qexists_tac `((p,d,h.inst_id),f,h,s)::pre` >>
      conj_tac >- (fs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
      Cases_on `run_inst_seq code u` >>
      simp[exec_result_map_def, trace_step_noninvoke, ADD_CLAUSES]) >>
  simp[create_trace_from_def] >>
  drule_then (fn th => simp[Once th, trace_step_noninvoke, Once exec_block_def])
    trace_block_visit
QED

Theorem internal_admin_visits[local]:
  EVERY (\(_,_,i,_). MEM i code) pre /\
  EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
               i.inst_opcode <> GAS) code ==>
  EVERY (\(_,_,i,s). inst_create_size_ok i s) pre /\
  create_cut_marks explicit pre = []
Proof
  simp[EVERY_MEM, FORALL_PROD, inst_create_size_ok_def, create_cut_marks_def] >>
  strip_tac >> conj_tac
  >- metis_tac[] >>
  `FILTER (\(_,_,i,_). i.inst_opcode = GAS) pre = []` suffices_by simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

(* Only capture, immutable reservation, parameter materialization, return
   scratch reservation and the transient lock contribute to [code]. No fuel
   is decremented inside that straight fragment. The INVOKE entry itself can
   be out of fuel; a supplied hit in its child excludes that case. If the
   lock aborts, the actual trace ends in [code] and cannot contain this hit. *)
Theorem create_cut_internal_selected_prologue:
  gas_invoke_entry (ctx,caller) s callee entered /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  trace_step p d fuel ctx caller inst s = inside ++ hit::suffix /\
  lookup_block entered.vs_current_bb callee.fn_blocks = SOME entry_bb /\
  isPREFIX code (DROP entered.vs_inst_idx entry_bb.bb_instructions) /\
  EVERY (\i. MEM i.inst_opcode
    [PARAM; RETPC_PARAM; ASSIGN; ALLOCA; MSTORE; TLOAD; EQ; ISZERO; ASSERT; TSTORE]) code /\
  (case hit of (_,_,i,t) => ~inst_create_size_ok i t) ==>
  ?k u pre before.
    fuel = SUC k /\ run_inst_seq code entered = OK u /\
    inside = pre ++ before /\ create_cut_marks explicit pre = [] /\
    create_trace_from ((d,inst.inst_id)::p) (SUC d) k ctx callee
      (u with vs_inst_idx := entered.vs_inst_idx + LENGTH code) =
      before ++ hit::suffix
Proof
  strip_tac >> drule_all create_cut_invoke_pending_entered >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
                i.inst_opcode <> GAS) code` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  drule_all straight_create_trace >>
  disch_then (qspecl_then [`((d,inst.inst_id)::p)`,`k`,`SUC d`,`ctx`] strip_assume_tac) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) internal_admin_visits >>
  rename1 `EVERY _ pre` >>
  `inside ++ [hit] ++ suffix = pre ++
    (case run_inst_seq code entered of
       OK u => create_trace_from ((d,inst.inst_id)::p) (SUC d) k ctx callee
                 (u with vs_inst_idx := entered.vs_inst_idx + LENGTH code)
     | _ => [])` by fs[] >>
  pop_assum (strip_assume_tac o REWRITE_RULE[APPEND_EQ_APPEND_MID])
  >- (PairCases_on `hit` >> gvs[]) >>
  Cases_on `run_inst_seq code entered` >> gvs[] >> metis_tac[]
QED

Theorem internal_fallthrough_terminal[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  (i.inst_opcode = RET \/ i.inst_opcode = INVALID) ==>
  create_trace_from p d k C f s = [((p,d,i.inst_id),f,i,s)]
Proof
  strip_tac >>
  simp[create_trace_from_def] >>
  drule_then (fn th => simp[Once th, Once exec_block_def,
    trace_step_noninvoke, step_inst_non_invoke, step_inst_base_opcode_eqs]) trace_block_visit >>
  Cases_on `eval_operands i.inst_operands s` >> gvs[] >>
  Cases_on `x` >> gvs[]
QED

(* The optional unlock may itself abort (for example in a static frame).
   In that case the RET/INVALID is not visited; either way the tail is safe. *)
Theorem create_cut_internal_fallthrough_no_hit:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  isPREFIX (unlock ++ [i]) (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\h. h.inst_opcode = TSTORE) unlock /\
  (i.inst_opcode = RET \/ i.inst_opcode = INVALID) /\
  create_trace_from p d k C f s = before ++ hit::after ==>
  case hit of (_,_,j,t) => inst_create_size_ok j t
Proof
  strip_tac >>
  `isPREFIX unlock (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[IS_PREFIX_APPEND1] >>
  `EVERY (\h. h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode) unlock /\
   EVERY (\h. h.inst_opcode <> CREATE /\ h.inst_opcode <> CREATE2 /\
                h.inst_opcode <> GAS) unlock` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  drule_all straight_create_trace >>
  disch_then (qspecl_then [`p`,`k`,`d`,`C`] strip_assume_tac) >>
  `EVERY (\(_,_,j,t). inst_create_size_ok j t) pre` by
    (drule_all internal_admin_visits >> simp[]) >>
  `EVERY (\(_,_,j,t). inst_create_size_ok j t) (create_trace_from p d k C f s)` suffices_by
    (PairCases_on `hit` >> gvs[EVERY_APPEND]) >>
  qpat_x_assum `create_trace_from p d k C f s = before ++ hit::after` kall_tac >>
  Cases_on `run_inst_seq unlock s` >> gvs[EVERY_APPEND] >>
  rename1 `run_inst_seq unlock s = OK u` >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[exec_block_run_inst_seq] >>
  `?rest. DROP (LENGTH unlock + s.vs_inst_idx) bb.bb_instructions = i::rest` by
    (qpat_assum `isPREFIX (unlock ++ [i]) _`
       (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     pure_rewrite_tac[GSYM DROP_DROP_T] >>
     qpat_assum `DROP _ _ = unlock ++ [i] ++ _` (pure_rewrite_tac o single) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `LENGTH unlock + s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >> fs[DROP_LENGTH_TOO_LONG]) >>
  qabbrev_tac `next = u with vs_inst_idx := LENGTH unlock + s.vs_inst_idx` >>
  `lookup_block next.vs_current_bb f.fn_blocks = SOME bb /\
   get_instruction bb next.vs_inst_idx = SOME i` by
    fs[Abbr `next`, get_instruction_def, DROP_CONS_EL] >>
  `create_trace_from p d k C f next = [((p,d,i.inst_id),f,i,next)]` by
    (irule internal_fallthrough_terminal >> metis_tac[]) >>
  simp[inst_create_size_ok_def]
QED
