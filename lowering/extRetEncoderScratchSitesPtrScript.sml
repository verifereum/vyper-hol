(* Compiler-region resources for recursive external-return encoding. *)
Theory extRetEncoderScratchSitesPtr
Ancestors
  extRetScratchResourcePtr abiEncoderWindowContract abiEncoderProps
  exprSimOperands venomMemDefs pred_set arithmetic

Theorem scratch_resource_restrict:
  scratch_resource ctx fn sites q len s /\ children SUBSET sites /\
  (len' <> 0 ==> len <> 0 /\ q <= q' /\ q'+len' <= q+len) ==>
  scratch_resource ctx fn children q' len' s
Proof
  simp_tac std_ss [scratch_resource_def, SUBSET_DEF] >> strip_tac >>
  conj_tac >- (rpt strip_tac >> res_tac >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `id IN sites` by metis_tac[] >>
  qpat_x_assum `!id b sz. _` drule_all >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED
