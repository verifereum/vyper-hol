(* Paired finite prefixes over arbitrary label maps and symbolic modes. *)
Theory fnFramePairedPrefixOwn
Ancestors
  frameJointTrace blockSimHelpers codegenSymRel asmSplice asmSpliceOwn
  asmSem asmSymSem list arithmetic

Theorem joint_trace_paired_prefix_own:
  !j.
  joint_trace vs0 ctx q0 evs qs qlast /\ j <= LENGTH evs /\
  R q0 a0 ss0 /\
  (!i a ss. i < j /\ R (EL i (q0::qs)) a ss ==>
    ?n a1 ss1.
      asm_steps lo (build_offset_to_pc prog) prog n a = AsmOK a1 /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
      R (EL (SUC i) (q0::qs)) a1 ss1) ==>
  ?n a ss.
    asm_steps lo (build_offset_to_pc prog) prog n a0 = AsmOK a /\
    sym_steps_mode allow_own prog env own n ss0 = SymOK ss /\
    R (EL j (q0::qs)) a ss
Proof
  Induct_on `j`
  >- (rpt strip_tac >> qexistsl [`0`, `a0`, `ss0`] >>
      simp[asm_steps_def, sym_steps_mode_def,
           asmSpliceTheory.sym_steps_def, sym_steps_own_def])
  >> rpt strip_tac
  >> `?n a ss.
        asm_steps lo (build_offset_to_pc prog) prog n a0 = AsmOK a /\
        sym_steps_mode allow_own prog env own n ss0 = SymOK ss /\
        R (EL j (q0::qs)) a ss` by
       (first_x_assum irule >> simp[])
  >> qpat_x_assum `!i a ss. _` (qspecl_then [`j`, `a`, `ss`] mp_tac)
  >> simp[] >> strip_tac
  >> qexistsl [`n + n'`, `a1`, `ss1`]
  >> metis_tac[asm_steps_compose_ok, sym_steps_mode_compose]
QED
