(* Zero compiler layouts under source widening; no copy semantics. *)
Theory externalReturnZeroLayout
Ancestors externalReturnDeclarationProvenance vyperTypeSystem compileEnv

Theorem return_arg_fits_zero_layout_mutual:
  (!phy dst. arg_type_fits phy dst ==>
    !ce. type_memory_bytes ce phy = 0 ==> type_memory_bytes ce dst = 0) /\
  (!ps ds. arg_types_fit ps ds ==>
    !ce. SUM (MAP (type_memory_bytes ce) ps) = 0 ==>
      SUM (MAP (type_memory_bytes ce) ds) = 0)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  simp[arg_type_fits_def, type_memory_bytes_def] >>
  simp[SF ETA_ss] >> metis_tac[]
QED

Theorem return_arg_fits_zero_layout:
  arg_type_fits phy dst /\ type_memory_bytes ce phy = 0 ==>
  type_memory_bytes ce dst = 0
Proof
  metis_tac[return_arg_fits_zero_layout_mutual]
QED

Theorem return_widens_zero_layout:
  type_widens_to tenv phy dst /\ type_memory_bytes ce phy = 0 ==>
  type_memory_bytes ce dst = 0
Proof
  simp[type_widens_to_def] >> metis_tac[return_arg_fits_zero_layout]
QED

Theorem return_bufferless_widenings_zero_layout:
  (phy = NoneT \/ type_memory_bytes ce phy = 0) /\
  type_widens_to tenv phy ann /\ type_widens_to tenv ann dst ==>
  type_memory_bytes ce ann = 0 /\ type_memory_bytes ce dst = 0
Proof
  strip_tac >>
  `type_memory_bytes ce phy = 0` by gvs[type_memory_bytes_def] >>
  metis_tac[return_widens_zero_layout]
QED
