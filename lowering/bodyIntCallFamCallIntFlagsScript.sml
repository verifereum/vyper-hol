(* Calling-convention flags, with arbitrary initial stack occupancy. *)
Theory bodyIntCallFamCallIntFlags
Ancestors
  compileEnv bodyIntCallMetadata bodyIntCallSource bodySim supportedNames
  supportedProgram context

Theorem intcall_pass_via_stack_word:
  !tys n i. i < LENGTH tys /\ EL i (compute_pass_via_stack tys n) ==>
    is_word_type (EL i tys)
Proof
  Induct_on `tys` >- simp[] >>
  rpt gen_tac >> simp[compute_pass_via_stack_def] >>
  IF_CASES_TAC >> Cases_on `i` >> simp[] >> metis_tac[]
QED

Theorem intcall_func_info_flags:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  ce.ce_func_info (nsid_to_string (NONE,name)) = (nret,rb,pvs) ==>
  LENGTH pvs = LENGTH args /\
  (!i. i < LENGTH args /\ EL i pvs ==> is_word_type (SND (EL i args)))
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def] >> drule supported_program_names >>
     simp[supported_declaration_names_def]) >>
  drule_at_then (Pat `MEM _ _`) mp_tac build_func_info_distinct >>
  simp[] >>
  disch_then (qspec_then `get_struct_fields ce.ce_struct_fields` mp_tac) >>
  fs[body_inv_def, nsid_to_string_def, compute_func_info_def] >>
  qpat_x_assum `ce.ce_func_info = _` (fn th => fs[th]) >>
  strip_tac >> gvs[] >> simp[LENGTH_compute_pass_via_stack] >>
  rpt strip_tac >>
  drule_at (Pat `EL _ _`) intcall_pass_via_stack_word >>
  simp[listTheory.EL_MAP]
QED

(* Source selection already exports exact actual/declaration type equality.
   Combine it with the metadata flags at the same selected declaration. *)
Theorem intcall_argument_flags:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Call ann (IntCall (src,name)) es dflt) st /\
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy name ts =
    SOME (mut,nr,args,dflts,ret,ss) /\
  ce.ce_func_info (nsid_to_string (src,name)) = (nret,rb,pvs) ==>
  MAP expr_type es = MAP SND args /\
  LENGTH pvs = LENGTH es /\
  (!i. i < LENGTH es /\ EL i pvs ==> is_word_type (expr_type (EL i es)))
Proof
  strip_tac >> drule_all body_intcall_source_selection >>
  strip_tac >> gvs[] >>
  drule_all intcall_func_info_flags >> strip_tac >> simp[] >>
  rpt strip_tac >>
  `EL i (MAP expr_type es) = EL i (MAP SND args)` by simp[] >>
  gvs[listTheory.EL_MAP]
QED
