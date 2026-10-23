(* Structural kwargs interface. These facts deliberately make no runtime
   decoding or source-evaluation claim. *)
Theory kwargBufferProps
Ancestors moduleLowering compileEnv context emitHelper finite_map list venomInst venomState vyperAST abiEncoder

Theorem compile_create_kwarg_allocas_names:
  !xs cenv st.
    MAP (\(name, p, ty, e). name)
      (FST (compile_create_kwarg_allocas cenv xs st)) =
    MAP (\(name, ty, e). name) xs
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  first_x_assum (qspecl_then [`cenv`, `cs'`] mp_tac) >> simp[]
QED

Theorem compile_create_kwarg_allocas_metadata:
  !xs cenv st.
    MAP (\(name, p, ty, e). (name, ty, e))
      (FST (compile_create_kwarg_allocas cenv xs st)) = xs
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  first_x_assum (qspecl_then [`cenv`, `cs'`] mp_tac) >> simp[]
QED

Theorem compile_create_kwarg_allocas_length:
  LENGTH (FST (compile_create_kwarg_allocas cenv xs st)) = LENGTH xs
Proof
  metis_tac[compile_create_kwarg_allocas_metadata, LENGTH_MAP]
QED

Theorem compile_register_kwarg_vars_fields:
  !xs cenv.
    (compile_register_kwarg_vars cenv xs).ce_struct_fields = cenv.ce_struct_fields
Proof
  Induct >> simp[compile_register_kwarg_vars_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[compile_register_kwarg_vars_def]
QED

Theorem compile_register_kwarg_vars_absent:
  !xs cenv name.
    ~MEM name (MAP (\(n,p,t,e). n) xs) ==>
    FLOOKUP (compile_register_kwarg_vars cenv xs).ce_vars name =
    FLOOKUP cenv.ce_vars name
Proof
  Induct >> simp[compile_register_kwarg_vars_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_register_kwarg_vars_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem compile_register_kwarg_vars_head:
  ~MEM name (MAP (\(n,p,t,e). n) rest) ==>
  FLOOKUP
    (compile_register_kwarg_vars cenv ((name, kw_ptr, ty, e)::rest)).ce_vars name =
  SOME (PtrVar kw_ptr (type_memory_bytes cenv ty))
Proof
  simp[compile_register_kwarg_vars_def, compile_register_kwarg_vars_absent,
       FLOOKUP_UPDATE]
QED

Theorem compile_create_kwarg_allocas_count:
  !xs cenv st.
    (SND (compile_create_kwarg_allocas cenv xs st)).cs_next_var =
    st.cs_next_var + LENGTH xs
Proof
  Induct >> simp[compile_create_kwarg_allocas_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_create_kwarg_allocas_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  first_x_assum (qspecl_then [`cenv`, `cs'`] mp_tac) >>
  gvs[compile_alloc_buffer_def, emit_op_def, fresh_id_def, fresh_var_def,
      emit_def, comp_bind_def, comp_return_def, comp_ignore_bind_def]
QED

(* Closed emission probes. Source positions include a 32-byte positional
   argument, so the first keyword head is at byte 36, not 4 or 40. *)
Definition kwarg_probe_state_def:
  kwarg_probe_state : compile_state =
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>
End

Definition kwarg_probe_vars_def:
  kwarg_probe_vars =
    [("b", Lit 128w, BaseT (UintT 256), Literal (BaseT (UintT 256)) (IntL 7));
     ("c", Lit 160w, BaseT (UintT 256), Literal (BaseT (UintT 256)) (IntL 9))]
End

Theorem compile_init_kwargs_zero_probe:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (SND (compile_init_kwargs ARB kwarg_probe_vars 36 0 (Lit 0w)
          kwarg_probe_state)).cs_current_insts =
    [(MSTORE, [Lit 128w; Lit 7w]); (MSTORE, [Lit 160w; Lit 9w])]
Proof
  EVAL_TAC >> simp[]
QED

Theorem compile_init_kwargs_partial_probe:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (SND (compile_init_kwargs ARB kwarg_probe_vars 36 1 (Lit 0w)
          kwarg_probe_state)).cs_current_insts =
    [(CALLDATALOAD, [Lit 36w]); (MSTORE, [Lit 128w; Var "%0"]);
     (MSTORE, [Lit 160w; Lit 9w])]
Proof
  EVAL_TAC >> simp[]
QED

Theorem compile_init_kwargs_full_probe:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (SND (compile_init_kwargs ARB kwarg_probe_vars 36 2 (Lit 0w)
          kwarg_probe_state)).cs_current_insts =
    [(CALLDATALOAD, [Lit 36w]); (MSTORE, [Lit 128w; Var "%0"]);
     (CALLDATALOAD, [Lit 68w]); (MSTORE, [Lit 160w; Var "%1"])]
Proof
  EVAL_TAC >> simp[]
QED

Theorem compile_init_kwargs_bytes_probe:
  MAP (\i. (i.inst_opcode, i.inst_operands))
    (SND (compile_init_kwargs ARB
      [("b", Lit 128w, BaseT (BytesT (Dynamic 10)),
        Literal (BaseT (BytesT (Dynamic 10))) (BytesL []))]
      36 1 (Lit 999w) kwarg_probe_state)).cs_current_insts =
    [(CALLDATALOAD, [Lit 36w]); (ADD, [Lit 4w; Var "%0"]);
     (CALLDATALOAD, [Var "%1"]); (GT, [Var "%2"; Lit 10w]);
     (ISZERO, [Var "%3"]); (ASSERT, [Var "%4"]);
     (CALLDATACOPY, [Lit 128w; Var "%1"; Lit 64w])]
Proof
  EVAL_TAC >> simp[]
QED

(* The static aggregate starts at the absolute head, and the following
   scalar starts after its 64-byte head. No extra selector adjustment. *)
Theorem compile_init_kwargs_static_probe:
  compile_init_kwargs ARB
    [("b", Lit 128w, ArrayT (BaseT (UintT 256)) (Fixed 2),
       Literal (BaseT (UintT 256)) (IntL 0))]
    36 1 (Lit 999w) kwarg_probe_state =
  compile_abi_decode_to_buf (Lit 128w) (Lit 36w) CALLDATALOAD (Lit 0w)
    (DecComplex F [(DecPrimWord NoClamp,32,32); (DecPrimWord NoClamp,32,32)])
    kwarg_probe_state
Proof
  EVAL_TAC >> simp[]
QED

Theorem compile_create_kwarg_allocas_probe:
  let (ds, st) = compile_create_kwarg_allocas ARB
    [("b", BaseT (UintT 256), Literal (BaseT (UintT 256)) (IntL 7));
     ("c", BaseT (BytesT (Dynamic 10)),
       Literal (BaseT (BytesT (Dynamic 10))) (BytesL []))] kwarg_probe_state in
  MAP (\(n,p,t,e). (n,p)) ds = [("b", Var "%0"); ("c", Var "%1")] /\
  MAP (\i. (i.inst_opcode, i.inst_operands)) st.cs_current_insts =
    [(ALLOCA, [Lit 32w]); (ALLOCA, [Lit 64w])]
Proof
  EVAL_TAC >> simp[]
QED

(* A build-time integrity check, not a proof oracle. Only the structural
   theorems of this theory are checked; upstream unrelated admissions are
   neither consumed by them nor hidden by this assertion. *)
val _ = List.app (fn (name, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle in kwargBufferProps: " ^ name))
  (DB.thms "kwargBufferProps");
