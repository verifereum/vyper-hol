Theory bodyPtrBytestringBuiltinsPlaceFrontierProbe
Ancestors bodyPtrBytestringBuiltinsImageFrontier
          bodyPtrBytestringBuiltinsCompilerAllocationTrace
          supportedProgram supportedExprs compileVyper vyperCompiler
          exprLowering compileEnv context emitHelper venomInst list

(* Concrete computation fixtures keep the repeated support/compiler checks
   about the same AST and metadata, without defining a reachability predicate. *)
Definition place_probe_tops_def:
  place_probe_tops =
    [StructDecl "A" [("first",BaseT (UintT 256)); ("second",BaseT (UintT 256))];
     StructDecl "B" [("only",BaseT (UintT 256))]]
End
Definition place_probe_base_def:
  place_probe_base = StructLit (StructT (NONE,"A")) (NONE,"B") []
End
Definition place_probe_expr_def:
  place_probe_expr = Attribute (BaseT (UintT 256)) place_probe_base "second"
End
Definition place_probe_env_def:
  place_probe_env = (ARB : compile_env) with
    ce_struct_fields := make_struct_fields_map place_probe_tops
End
Definition place_probe_final_def:
  place_probe_final = (initial_compile_state "") with
    <|cs_next_var := 2; cs_next_id := 2;
      cs_current_insts := [mk_inst 0 ALLOCA [Lit 32w] ["%0"];
                           mk_inst 1 ADD [Var "%0"; Lit 32w] ["%1"]]|>
End

Theorem place_probe_supported:
  supported_program place_probe_tops /\
  supported_pure_expr place_probe_tops place_probe_base /\
  supported_place_expr place_probe_tops place_probe_base /\
  supported_pure_expr place_probe_tops place_probe_expr
Proof
  EVAL_TAC
QED

Theorem place_probe_compile:
  !ty. compile_expr place_probe_env ty place_probe_expr (initial_compile_state "") =
    (LocatedValue (BaseT (UintT 256)) (mk_ptr (Var "%1") LocMemory),place_probe_final)
Proof
  EVAL_TAC >> simp[]
QED

Theorem place_probe_short_list:
  !xs. LENGTH xs < 3 ==> ~image_bad xs /\ ~image_pending3 xs
Proof
  simp[image_bad_def, image_pending3_def] >> rpt strip_tac >>
  qpat_x_assum `_ = _ ++ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
  simp[]
QED

Theorem place_probe_frontier:
  image_entry (initial_compile_state "") /\
  image_pending2 place_probe_final.cs_current_insts /\
  ~image_pending3 place_probe_final.cs_current_insts /\
  ~image_bad place_probe_final.cs_current_insts /\
  ~image_entry place_probe_final
Proof
  simp[place_probe_final_def, initial_compile_state_def, image_entry_def,
    place_probe_short_list]
QED

Theorem place_probe_trace:
  allocation_trace (initial_compile_state "") place_probe_final
Proof
  mp_tac bodyPtrBytestringBuiltinsCompilerAllocationTraceTheory.compile_expr_allocation_trace >>
  disch_then (qspecl_then [`place_probe_env`, `NoneT`, `place_probe_expr`,
    `initial_compile_state ""`] mp_tac) >>
  pure_rewrite_tac[place_probe_compile, pairTheory.SND] >> simp[]
QED
