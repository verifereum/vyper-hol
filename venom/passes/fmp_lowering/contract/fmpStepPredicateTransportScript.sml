(* Pointwise instruction invariants across rewriting and root installation. *)
Theory fmpStepPredicateTransport
Ancestors
  fmpStepRewrite fmpLowerDefs o1PassContract venomInst list rich_list

Theorem fmp_install_root_every:
  EVERY (\bb. EVERY P bb.bb_instructions) blocks /\
  EVERY P (OPTION_TO_LIST root) /\ EVERY P (OPTION_TO_LIST pc) /\
  fmp_install_root ctx fn (FmpRootLayout n root pc t) blocks = SOME (out,t') ==>
  EVERY (\bb. EVERY P bb.bb_instructions) out
Proof
  Cases_on `blocks` >> simp[fmp_install_root_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `fn_is_context_entry ctx fn` >> simp[EVERY_APPEND] >>
  gvs[EVERY_MEM] >> metis_tac[MEM_TAKE, MEM_DROP_IMP]
QED

Theorem fmp_lower_function_every:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  EVERY P (fn_insts fn) /\
  (!infos runner t i head t'. MEM i (fn_insts fn) /\
    fmp_lower_inst infos ctx runner t i = SOME (head,t') ==> EVERY P head) /\
  (!runner t bases out t'.
    fmp_emit_restores runner t bases = (out,t') ==> EVERY P out) /\
  (!info runner t n root pc t'.
    fmp_make_root_layout ctx fn info runner t = SOME (FmpRootLayout n root pc t') ==>
    EVERY P (OPTION_TO_LIST root) /\ EVERY P (OPTION_TO_LIST pc)) ==>
  EVERY P (fn_insts fn')
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[fmp_checked_seal_def, fmp_seal_def, fn_insts_def, AllCaseEqs()] >>
  Cases_on `root_layout` >> gvs[] >>
  drule fmp_lower_blocks_every >>
  disch_then (qspec_then `P` mp_tac) >>
  (impl_tac >- (rpt strip_tac >>
    gvs[fn_insts_blocks_MEM] >> metis_tac[])) >>
  strip_tac >>
  qpat_x_assum `!info runner t n root pc t'. _` drule >> strip_tac >>
  drule_all fmp_install_root_every >>
  simp[EVERY_MEM, fn_insts_blocks_MEM] >> metis_tac[]
QED
