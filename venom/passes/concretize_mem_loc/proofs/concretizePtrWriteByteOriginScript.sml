Theory concretizePtrWriteByteOrigin
Ancestors concretizePtrSelectedOrigin ptrDiscipline concretizeMemLocDefs
  pointerConfinedDefs venomWf venomInst list pred_set finite_map words

Theorem ptr_write_byte_selected_site:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  lo <= x /\ x IN range_bytes (source_memory_write_ranges inst s) ==>
  ?v b sz. inst_write_op inst = SOME (Var v) /\
    FLOOKUP G v = SOME (b,sz) /\ b <= x /\ x < b + sz
Proof
  simp[range_bytes_def] >> strip_tac >>
  `len <> 0 /\ lo < off + len` by decide_tac >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges _ _) /\ _ ==> _`
    (qspecl_then [`off`, `len`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`v`, `b`, `sz`] >> simp[inst_write_op_def] >> decide_tac
QED

Theorem ptr_frame_write_byte_origin:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  fn_ptr_ok P fn /\ wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\ MEM inst (fn_insts fn) /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  lo <= x /\ x IN range_bytes (source_memory_write_ranges inst s) ==>
  ?v b sz. inst_write_op inst = SOME (Var v) /\
    FLOOKUP G v = SOME (b,sz) /\ b <= x /\ x < b + sz /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
       ml_used_gen (Allocation aid)
         (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems inst) \/
     (?i idx r. MEM i (fn_insts fn) /\ i.inst_opcode = PARAM /\
       i.inst_operands = [Lit idx] /\ MEM r i.inst_outputs /\
       w2n idx < LENGTH PG /\ EL (w2n idx) PG = SOME (b,sz) /\
       v IN pointer_derived_vars fn {r}))
Proof
  strip_tac >> drule_all ptr_write_byte_selected_site >> strip_tac >>
  qexistsl [`v`, `b`, `sz`] >> simp[] >>
  irule ptr_frame_write_selected_origin >> simp[] >> metis_tac[]
QED

(* The history byte witness does not yet supply the observation's PG/G or
   an actual frame_reachable derivation at that observation. These must be
   recovered from history chronology before applying this boundary.
   Revert forwarding is excluded because access_ok guards its range clauses.
   Completed INVOKE histories and the imported PARAM-to-caller argument
   linkage remain unresolved; a bare call barrier is not a per-site seed.
   The selected site contains x, but no separate fresh site's identity is
   inferred from numeric overlap. The lo bound must come from the caller's
   allocation invariant, never from a zero allocator initialization. *)
