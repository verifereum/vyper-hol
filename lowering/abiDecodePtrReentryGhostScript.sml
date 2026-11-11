(* Pruning only dead future variables preserves the live ghost invariant. *)
Theory abiDecodePtrReentryGhost
Ancestors
  abiDecodePtrReentryObservations abiDecoderReentry abiDecoderVarExtend
  bodyPtrDefs compileEnv venomState finite_map pred_set list

Theorem abi_decode_ptr_prune_covers:
  abi_decoder_operand_live next (Var p) ==>
  (ptr_covers G tn p (abi_decoder_prune_vars next s) sz <=> ptr_covers G tn p s sz)
Proof
  simp[abi_decoder_operand_live_def, abi_decoder_prune_vars_def,
       ptr_covers_def, lookup_var_def, FLOOKUP_DRESTRICT]
QED

Theorem abi_decode_ptr_prune_ghost:
  ghost_inv d cenv cx es G tn s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_decoder_operand_live next (Var p)) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
    abi_decoder_operand_live next (Var p)) ==>
  ghost_inv d cenv cx es G tn (abi_decoder_prune_vars next s)
Proof
  rw[ghost_inv_def]
  >- (irule (iffRL abi_decode_ptr_prune_covers) >> metis_tac[])
  >- (fs[abi_decoder_prune_vars_def, lookup_var_def, FLOOKUP_DRESTRICT,
         AllCaseEqs()] >> metis_tac[])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >>
      rename1 `cenv.ce_return_buf = SOME (PtrVar (Var p) slot_size)` >>
      `abi_decoder_operand_live next (Var p)` by metis_tac[] >>
      gvs[abi_decoder_prune_vars_def, abi_decoder_operand_live_def,
          ptr_covers_def, lookup_var_def, FLOOKUP_DRESTRICT])
  >> fs[stor_taint_ok_def, abi_decoder_prune_vars_def]
QED

(* The compiler-side age facts already required at decoder entry discharge
   the internal pruning liveness conditions. *)
Theorem abi_decode_ptr_prune_ghost_reserved:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv st /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p) ==>
  ghost_inv d cenv cx es G tn (abi_decoder_prune_vars st.cs_next_var s)
Proof
  strip_tac >> irule abi_decode_ptr_prune_ghost >> simp[] >>
  fs[local_ptrs_reserved_def, not_fresh_at_def,
     abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> metis_tac[]
QED
