(* Actual execution transport for one retained-callee site replacement. *)
Theory functionInlinerSiteSimulation
Ancestors
  functionInlinerSimulation functionInlinerContextTransport ctxLookupAgreeHelpers
  venomExecSemantics venomInst list

Definition inline_lower_instruction_def:
  inline_lower_instruction ctx0 C n rank bound i <=>
    ?h. MEM h C.ctx_functions /\ qualified_origin ctx0 n h /\
        fcg_is_reachable (fcg_analyze ctx0) h.fn_name /\
        (rank : string -> num) h.fn_name < bound /\ MEM i (fn_insts h)
End

Theorem inline_lower_instruction_closed[local]:
  inliner_input_ok ctx0 /\
  (!h. MEM h C.ctx_functions ==> qualified_origin ctx0 n h) /\
  (!a b. MEM b (fcg_get_callees (fcg_analyze ctx0) a) ==>
    (rank : string -> num) b < rank a) /\
  lookup_function caller.fn_name C.ctx_functions = SOME caller /\
  final.fn_name = caller.fn_name ==>
  !i nm ops.
    inline_lower_instruction ctx0 C n rank (rank caller.fn_name) i /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) ==>
    lookup_function nm C.ctx_functions =
      lookup_function nm (site_replace C caller final).ctx_functions /\
    (!h. lookup_function nm C.ctx_functions = SOME h ==>
      EVERY (inline_lower_instruction ctx0 C n rank (rank caller.fn_name))
        (fn_insts h))
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  fs[inline_lower_instruction_def] >>
  `i.inst_operands = Label nm::ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `rank nm < rank h.fn_name` by
    metis_tac[qualified_origin_retained_call_rank] >>
  `fcg_is_reachable (fcg_analyze ctx0) nm` by
    metis_tac[qualified_origin_retained_call_reachable] >>
  `nm <> caller.fn_name` by (strip_tac >> gvs[]) >>
  conj_tac
  >- (drule_all site_replace_lookup >> simp[]) >>
  rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  irule (iffRL inline_lower_instruction_def) >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  qexists `callee` >>
  `MEM callee C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `callee.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  simp[]
QED

Theorem inline_lower_run_context:
  inliner_input_ok ctx0 /\
  (!h. MEM h C.ctx_functions ==> qualified_origin ctx0 n h) /\
  (!a b. MEM b (fcg_get_callees (fcg_analyze ctx0) a) ==>
    (rank : string -> num) b < rank a) /\
  lookup_function caller.fn_name C.ctx_functions = SOME caller /\
  final.fn_name = caller.fn_name /\
  MEM fn C.ctx_functions /\
  fcg_is_reachable (fcg_analyze ctx0) fn.fn_name /\
  rank fn.fn_name < rank caller.fn_name ==>
  run_blocks fuel C fn s = run_blocks fuel (site_replace C caller final) fn s
Proof
  strip_tac >> irule (cj 3 run_defs_predicate_cong) >>
  qexists `inline_lower_instruction ctx0 C n rank (rank caller.fn_name)` >>
  conj_tac
  >- (metis_tac[inline_lower_instruction_closed]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  simp[inline_lower_instruction_def] >> qexists `fn` >> simp[]
QED
