(* A representation diagnostic, not a counterexample to the stage contract. *)
Theory lowerDloadSiteDiagnostic
Ancestors
  lowerDloadAllocation finite_map pred_set arithmetic

Theorem ld_alloc_account_not_functional_site:
  !s t.
  let src = s with <| vs_allocas := FEMPTY |+ (0, (0,0)) |+ (1, (0,0));
                      vs_alloca_next := 0 |>;
      tgt = t with <| vs_allocas := FEMPTY |+ (0, (0,0)) |+ (1, (32,0))
                                             |+ (2, (0,32));
                      vs_alloca_next := 32 |>
  in ld_alloc_account {2} 0 {2} src tgt /\
     ~(?B. !id bs sz. FLOOKUP src.vs_allocas id = SOME (bs,sz) ==>
                    FLOOKUP tgt.vs_allocas id = SOME (B (bs,sz),sz))
Proof
  simp[LET_THM, ld_alloc_account_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (conj_tac >- SET_TAC[] >> rpt strip_tac >>
      Cases_on `id = 1` >- (gvs[] >> qexists_tac `32` >> simp[]) >>
      Cases_on `id = 0` >> gvs[] >> qexists_tac `0` >> simp[]) >>
  gen_tac >> Cases_on `B (0,0) = 0`
  >- (qexistsl [`1`, `0`, `0`] >> simp[]) >>
  qexistsl [`0`, `0`, `0`] >> simp[]
QED

(* Interface audit (C1.2.5.5.4.5).

   Representation witness versus execution:
   exec_alloca_def (venomExecSemantics, 535-552) records a fresh ID at the
   frontier and increments by w2n size. With empty maps/frontier 0, fresh
   ordinary ID 0 of size 0 records (0,0), leaving frontier 0. Source DLOAD
   reads only the data section (944-948), so ordinary ID 1 of size 0 also
   records (0,0). In lower_dload_inst_supply_def (139-174), the intervening
   DLOAD instead introduces a fresh ALLOCA 32; ADD/CODECOPY/MLOAD do not
   change the allocation map/frontier. Thus the target has ordinary ID 0
   at (0,0), scratch ID 2 at (0,32), ordinary ID 1 at (32,0), frontier 32.
   The finite-map witness above is exactly this allocation projection.
   This is not a claim of a full reachable o1_src_inv witness.

   out_prov_def (ptrDiscipline, 169-186) assigns ALLOCA its map pair,
   DALLOCA (w2n result, w2n new_fmp - w2n result), and PARAM its inherited
   PG entry; ASSIGN/ADD/SUB copy first_prov. DALLOCA 0 leaves fmp unchanged
   and yields an empty site; numeric coincidence with an empty ALLOCA or
   an inherited empty parameter is not excluded by that definition.
   Nonzero DALLOCA wrap also needs a raw invariant before natural
   subtraction represents size. access_ok's 0 < sz condition applies to
   LT/GT/EQ, not arbitrary provenance propagation. A relation permitting
   multiple targets for empty source pairs removes this witness, but is
   not yet sufficient: caller parameters outlive frame changes, callee
   return restores caller maps/frontiers without restoring memory, and
   repeated calls may reuse numeric sites. Live-frame/lifetime ownership
   is still necessary for nonempty-site geometry and memory taint.

   Exhaustive opcode partition, checked against venomInstScript 24-69
   and step_inst_base_def 559-1125 (INVOKE is handled by step_inst):

   1. Scalar arithmetic/bitwise:
      MUL Div SDIV Mod SMOD Exp ADDMOD MULMOD AND OR XOR NOT ISZERO
      SIGNEXTEND BYTE.
      Need clean nonpointer operands from ptr_use_ok and taint_ok; then
      scalar evaluation equality, deterministic output and empty mask.
      No memory range or external state. Operand lemmas are consumers;
      reachable classification/cleanliness producer still missing.
   2. Affine pointers: ADD SUB OFFSET.
      ADD/SUB need affine_pointer_ops classification (pointer+scalar,
      pointer-scalar, not scalar-pointer) and coherent paired provenance.
      OFFSET has no provenance propagation in out_prov; ptr_use_ok must
      exclude pointer use (it is not a memory access). Clean scalars use
      family 1.
      No memory/external effects. Reachable paired provenance is missing.
   3. Comparisons: EQ LT GT SLT SGT.
      Unsigned pointer comparison needs shared positive site, endpoint and
      nonwrap bounds, plus UNIQUE target for this nonempty live site.
      SLT/SGT must be scalar by ptr_use_ok. All outputs scalar/empty mask.
      Geometry/uniqueness producers remain missing.
   4. Shifts: SHL SHR SAR.
      Shift count must be clean; shifted scalar may be masked. Need byte
      shift preservation and mask monotonicity, not whole-word equality.
      shift_taint_def 319-329 transports each bit of each source byte;
      SAR additionally taints sign fill when source byte 0 is tainted.
      For k>=256 and valid byte masks (i<32), SHL/SHR yield no taint;
      SAR fills every byte iff 0 is tainted. Mask validity and byte-level
      shift laws still need producers. No memory/external effects.
   5. SSA: ASSIGN PHI.
      Copy paired values/provenance/masks; PHI uses previous-block parallel
      environments, not sequential step_inst_base (which errors for PHI).
      Update consumer exists; parallel selection/control producer missing.
   6. Local memory: MLOAD MSTORE MSTORE8 MCOPY ILOAD ISTORE.
      Need paired address ranges, nonwrap/containment, disjoint live sites,
      byte relation, masked word load/store/copy laws; MSTORE8 uses low
      byte, not a whole word. ILOAD/ISTORE addresses fixed, not relocated;
      ISTORE also updates immutable bookkeeping. No oracle effects.
      Reachable range correspondence and bookkeeping producers missing.
   7. Storage: SLOAD SSTORE TLOAD TSTORE.
      Keys clean/equal, byte-masked values; matched storage/transient maps
      and key_update transport. No memory geometry; map producers missing.
   8. Copies: CALLDATACOPY RETURNDATACOPY CODECOPY EXTCODECOPY.
      Destination range geometry and clean source offsets/lengths; input
      bytes agree outside source taint. Returndata length/OOB abort must
      match. EXTCODECOPY additionally needs account-code agreement.
      Missing range, length, code/account/returndata state producers.
   9. Data expansion: DLOAD DLOADBYTES.
      Separate phase certificate and data/code_end agreement. Scratch
      overwrite consumer exists; phase coverage/range producers missing.
      Malformed envelopes are kept by lowering and must match error paths.
  10. Allocator/FMP: ALLOCA DALLOCA GETFMP SETFMP INITIAL_FMP BUMP MEMTOP.
      ALLOCA needs paired fresh/repeated sites and headroom, including zero
      size. DALLOCA needs fmp equality/nonwrap and live-site ownership.
      INITIAL_FMP/BUMP need initial cursor/paired values and two updates.
      MEMTOP and raw GETFMP/SETFMP are excluded by source shape/discipline;
      must explicitly derive exclusions, not assume memory lengths equal.
      Accounting consumers exist, reachable ownership producer missing.
  11. Parameters/internal calls: PARAM FMP_PARAM RETPC_PARAM INVOKE RET
      RETFMP DRET.
      PARAM needs paired PG/value entries. Hidden params require static
      pointer exclusion. INVOKE/returns require saved caller relation,
      inherited provenance, return values/taints, fmp adoption/reset and
      frame restoration. DRET excluded by fn_ptr_ok. No ordinary opcode
      argument supplies stack lifetime or oracle reset agreement.
  12. Control/termination: JMP JNZ DJMP STOP SINK RETURN REVERT ASSERT
      ASSERT_UNREACHABLE INVALID NOP.
      Same labels/clean branch selectors (and DJMP bounds), matched control
      location. RETURN/REVERT need corresponding memory slice/length and
      final taint transport; revert forwarding needs exceptional terminal
      alternative. Halt/revert external-state fields must be related.
      Missing control, final-state and exceptional-path producers.
  13. Environment/data reads: CALLER CALLVALUE ADDRESS ORIGIN GASPRICE GAS
      GASLIMIT COINBASE TIMESTAMP NUMBER PREVRANDAO CHAINID SELFBALANCE
      BALANCE BLOCKHASH BASEFEE CODESIZE EXTCODESIZE EXTCODEHASH BLOBHASH
      BLOBBASEFEE CALLDATALOAD CALLDATASIZE RETURNDATASIZE.
      Clean scalar arguments where present; equal call/tx/block context,
      accounts/code/calldata, or matched returndata length. No provenance
      output or memory write. External field/length producers missing.
  14. Observable effects: SHA3 LOG SELFDESTRUCT CALL STATICCALL DELEGATECALL
      CREATE CREATE2.
      Clean keys/topics/scalars and related memory input ranges (taint_ok
      excludes tainted hash/log input outside revert exception). Account,
      log and oracle request agreement; external result/adopt_reset and
      output-memory taint transport. CREATE/delegate require empty source
      storage/transient taint. Missing request, oracle and range producers.

   Every datatype constructor occurs in exactly one family above. All
   malformed arity/output/undefined-operand cases must match by identical
   static envelopes and synchronized operand definedness; INVOKE's base
   unknown-opcode branch is bypassed only in the higher-level semantics.
   None of these obligations follow from allocation accounting alone.
*)
