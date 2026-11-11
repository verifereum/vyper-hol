(*
 * Fuel bound for the static-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_sarray_typed
 *)

Theory fragFuelLoopSarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  typedCopyLoopLayoutPtr
Libs
  fragFuelLib

(* The layout theorem is purely symbolic: its only non-definitional premise
   is the slow-branch guard.  It uses compile_copy_sarray_typed_slow, whose
   proof is one unfolding of compile_store_memory_typed_def. *)
Theorem sarray_slow_structure[local]:
  (!d s Wv E. fuel_ok Wv {} E
      (compile_store_memory_typed ce d dt s st)) /\
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt) /\
  compile_copy_sarray_typed ce dst dt src st n sa = ((),sz) ==>
  cs_extends sa sz /\ sa.cs_next_var <= sz.cs_next_var /\
  (cs_no_phi sa ==> cs_no_phi sz)
Proof
  strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  `cs_extends si se /\ si.cs_next_var <= se.cs_next_var /\
   (cs_no_phi si ==> cs_no_phi se)` by
    (qpat_x_assum `!d s Wv E. _` (qspecl_then [`Var dp`, `Var sp`, `{}`, `{}`] mp_tac) >>
     pure_rewrite_tac[fuel_ok_def] >> disch_then drule >> metis_tac[]) >>
  (* These frontier facts also apply to the witnesses reused by the runtime
     proof: the counter is below both ends of the recursive child. *)
  `si.cs_next_var = sa.cs_next_var + 7 /\
   sa.cs_next_var < si.cs_next_var /\ sa.cs_next_var < se.cs_next_var` by
    (gvs[] >> decide_tac) >>
  `cs_extends sa si` by
    (simp[cs_extends_def] >>
     qexists_tac `TAKE 2 si.cs_blocks` >> simp[]) >>
  `cs_extends se sz` by
    (simp[cs_extends_def] >> qexists_tac `[HD sz.cs_blocks]` >> simp[]) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- gvs[] >>
  strip_tac >>
  `cs_no_phi si` by
    (simp[cs_no_phi_def, venomInstTheory.mk_inst_def] >>
     gvs[cs_no_phi_def]) >>
  `cs_no_phi se` by metis_tac[] >>
  simp[cs_no_phi_def, venomInstTheory.mk_inst_def] >>
  gvs[cs_no_phi_def]
QED

(* Given a bound for the element copy (the recursive call), the copy of a
   static array of n elements is bounded.  The slow path counts a fresh
   counter from 0 while it is below the literal n2w n; each round copies one
   element and adds 1, so the loop leaves within 2 ** 256 rounds, and the
   counter never wraps since it stays at most n2w n. *)
Theorem fuel_ok_compile_copy_sarray_typed:
  !cenv dst dst_elem src src_elem n.
    (!d s Wv E. fuel_ok Wv {} E
                  (compile_store_memory_typed cenv d dst_elem s src_elem)) ==>
    !Wv E. fuel_ok Wv {} E
             (compile_copy_sarray_typed cenv dst dst_elem src src_elem n)
Proof
  cheat
QED
