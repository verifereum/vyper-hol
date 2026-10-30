(*
 * Every entry holds its locals through pointer variables (#636)
 *
 * build_compile_env places a function's parameters at fixed MemLoc slots
 * (build_compile_env_vars).  The statement and expression simulations
 * relate only locals held through a pointer variable (local_ptrs_rel), and
 * take local_ptrs_reserved, which rules out any MemLoc variable, at the
 * start of the code they simulate.  Each entry kind's prologue rebinds
 * every parameter to a pointer variable of its own before the body:
 *   - an external function, with or without default arguments:
 *     compile_register_positional_args decodes every parameter, defaulted
 *     ones included, into an ALLOCA;
 *   - the constructor: compile_register_constructor_args does the same
 *     from the data section;
 *   - an internal function, at runtime or in the constructor:
 *     materialize_internal_params (package_internal_fn_prologue_code and
 *     package_internal_fn_prologue_ptrs in intCallCallee);
 *   - the fallback (__default__) has no parameters, so its compile env
 *     holds no MemLoc variable to begin with.
 * compile_register_kwarg_vars, which keeps default arguments at MemLoc
 * slots, has no caller in the current lowering.
 *
 * TOP-LEVEL:
 *   compile_register_positional_args_reserved,
 *   compile_register_constructor_args_reserved
 *                           -- registration leaves no MemLoc variable it
 *                              was given, and every variable it rebinds is
 *                              a pointer variable handed out before the end
 *   external_entry_locals   -- local_ptrs_reserved at the start of an
 *                              external body, every parameter a pointer
 *                              variable
 *   constructor_entry_locals -- the same for the constructor body
 *   fallback_entry_locals   -- local_ptrs_reserved for the fallback body
 *)
Theory entryLocals
Ancestors
  list finite_map
  compileEnv compileVyper moduleLowering context abiEncoder emitHelper
  exprLoweringProps loweringHalt intCallCallee
Libs
  monadsyntax

(* ===== The compiler counter across argument decoding ===== *)

Theorem emit_op_next_var[local]:
  !opc ops st x st'.
    emit_op opc ops st = (x, st') ==> st.cs_next_var <= st'.cs_next_var
Proof
  rpt strip_tac >> qspecl_then [`opc`, `ops`, `st`] mp_tac ci_mono_emit_op >>
  simp[ci_mono_def]
QED

Theorem emit_void_next_var[local]:
  !opc ops st x st'.
    emit_void opc ops st = (x, st') ==> st.cs_next_var <= st'.cs_next_var
Proof
  rpt strip_tac >> qspecl_then [`opc`, `ops`, `st`] mp_tac ci_mono_emit_void >>
  simp[ci_mono_def]
QED

Theorem compile_abi_decode_to_buf_next_var[local]:
  !dst src opc hi info st x st'.
    compile_abi_decode_to_buf dst src opc hi info st = (x, st') ==>
    st.cs_next_var <= st'.cs_next_var
Proof
  rpt strip_tac >>
  qspecl_then [`dst`, `src`, `opc`, `hi`, `info`, `st`] mp_tac
    (cj 1 ci_mono_compile_abi_decode) >>
  simp[ci_mono_def]
QED

Theorem compile_abi_clamp_basetype_next_var[local]:
  !cl op st x st'.
    compile_abi_clamp_basetype op cl st = (x, st') ==>
    st.cs_next_var <= st'.cs_next_var
Proof
  Cases >> rpt gen_tac >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  TRY (rename1 `if signed then _ else _` >> Cases_on `signed`) >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem compile_decode_args_next_var[local]:
  !args cenv off opc hi adj st x st'.
    compile_decode_args cenv args off opc hi adj st = (x, st') ==>
    st.cs_next_var <= st'.cs_next_var
Proof
  Induct >- simp[compile_decode_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[comp_bind_def, comp_ignore_bind_def,
                            comp_return_def]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emit_op_next_var >> imp_res_tac emit_void_next_var >>
  imp_res_tac compile_abi_decode_to_buf_next_var >>
  imp_res_tac compile_abi_clamp_basetype_next_var >>
  res_tac >> gvs[comp_return_def] >> decide_tac
QED

(* ===== Registration ===== *)

(* One registration step: binding name to a fresh ALLOCA's pointer keeps
   the registration's invariant: a MemLoc variable is one still to be
   registered, and the pointer variables were handed out before the
   current state, one per variable.  The decoding after the ALLOCA only
   moves the counter on. *)
Theorem register_ptr_step[local]:
  !cenv name names msz st buf sa sb.
    compile_alloc_buffer msz st = (buf, sa) /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!n off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ==>
                n = name \/ MEM n names) /\
    (!n1 n2 p sz1 sz2.
       FLOOKUP cenv.ce_vars n1 = SOME (PtrVar (Var p) sz1) ==>
       not_fresh_at st p /\
       (FLOOKUP cenv.ce_vars n2 = SOME (PtrVar (Var p) sz2) ==> n1 = n2)) ==>
    (!n off sz.
       FLOOKUP (cenv.ce_vars |+ (name, PtrVar buf.buf_operand msz)) n =
         SOME (MemLoc off sz) ==> MEM n names) /\
    (!n1 n2 p sz1 sz2.
       FLOOKUP (cenv.ce_vars |+ (name, PtrVar buf.buf_operand msz)) n1 =
         SOME (PtrVar (Var p) sz1) ==>
       not_fresh_at sb p /\
       (FLOOKUP (cenv.ce_vars |+ (name, PtrVar buf.buf_operand msz)) n2 =
          SOME (PtrVar (Var p) sz2) ==> n1 = n2)) /\
    ?p. buf.buf_operand = Var p
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!y. not_fresh_at sa y ==> not_fresh_at sb y` by
    (rw[not_fresh_at_def] >> first_x_assum irule >> decide_tac) >>
  simp[FLOOKUP_UPDATE] >> rpt conj_tac
  >- (rw[] >> res_tac >> gvs[])
  >- (rpt gen_tac >> rw[] >> gvs[] >> metis_tac[])
QED

(* compile_register_positional_args and compile_register_constructor_args
   differ only in where compile_decode_args reads, so one induction proves
   both. *)
fun register_args_reserved_tac def =
  Induct
  >- (simp[def, comp_return_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  PairCases >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (cenv', st')` mp_tac >>
  simp[Once def] >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >> simp[]
  >- (strip_tac >> first_x_assum drule >> impl_tac
      >- (conj_tac >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
                       gvs[var_location_memory_size_def]) >>
          metis_tac[]) >>
      simp[]) >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[]
  >- (strip_tac >> first_x_assum drule >> impl_tac
      >- (conj_tac >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
                       gvs[var_location_memory_size_def]) >>
          metis_tac[]) >>
      simp[]) >>
  rename1 `var_location_memory_size loc = SOME msz` >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule compile_decode_args_next_var >> strip_tac >>
  rename1 `compile_alloc_buffer msz st = (buf, sa)` >>
  rename1 `compile_decode_args _ _ _ _ _ _ sa = ((), sb)` >>
  qspecl_then [`cenv`, `h0`, `MAP FST args`, `msz`, `st`, `buf`, `sa`,
               `sb`] mp_tac register_ptr_step >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  last_x_assum drule >> impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!n. _ \/ _ ==> _` mp_tac >>
  qpat_x_assum `buf.buf_operand = _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> first_x_assum irule >>
  Cases_on `n = h0` >> gvs[FLOOKUP_UPDATE];

Theorem compile_register_positional_args_reserved:
  !args cenv off st cenv' st'.
    compile_register_positional_args cenv args off st = (cenv', st') /\
    (!n off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ==>
                MEM n (MAP FST args)) /\
    (!n1 n2 p sz1 sz2.
       FLOOKUP cenv.ce_vars n1 = SOME (PtrVar (Var p) sz1) ==>
       not_fresh_at st p /\
       (FLOOKUP cenv.ce_vars n2 = SOME (PtrVar (Var p) sz2) ==> n1 = n2)) ==>
    local_ptrs_reserved cenv' st' /\
    !n. (?off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz)) \/
        (?p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz)) ==>
        ?p sz. FLOOKUP cenv'.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  register_args_reserved_tac compile_register_positional_args_def
QED

Theorem compile_register_constructor_args_reserved:
  !args cenv off dsz st cenv' st'.
    compile_register_constructor_args cenv args off dsz st = (cenv', st') /\
    (!n off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ==>
                MEM n (MAP FST args)) /\
    (!n1 n2 p sz1 sz2.
       FLOOKUP cenv.ce_vars n1 = SOME (PtrVar (Var p) sz1) ==>
       not_fresh_at st p /\
       (FLOOKUP cenv.ce_vars n2 = SOME (PtrVar (Var p) sz2) ==> n1 = n2)) ==>
    local_ptrs_reserved cenv' st' /\
    !n. (?off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz)) \/
        (?p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz)) ==>
        ?p sz. FLOOKUP cenv'.ce_vars n = SOME (PtrVar (Var p) sz)
Proof
  register_args_reserved_tac compile_register_constructor_args_def
QED

(* ===== Each entry kind ===== *)

Theorem build_positional_args_FST[local]:
  !cenv fargs. MAP FST (build_positional_args cenv fargs) = MAP FST fargs
Proof
  Induct_on `fargs` >> fs[build_positional_args_def] >>
  PairCases >> fs[build_positional_arg_def]
QED

(* An external function's body, with or without default arguments, starts
   with every parameter held through a pointer variable and no MemLoc
   variable: what the simulations take of the locals. *)
Theorem external_entry_locals:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   lbl cenv0 pos_args rest st cenv st'.
    package_external_fn tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, fbody) =
      (lbl, cenv0, pos_args, rest) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, st') ==>
    local_ptrs_reserved cenv st' /\
    EVERY (\a. ?p sz. FLOOKUP cenv.ce_vars (FST a) = SOME (PtrVar (Var p) sz))
      fargs
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops External mut fname fargs ret fbody
                      use_trans).ce_vars /\
   pos_args = build_positional_args cenv0 fargs` by
    (gvs[package_external_fn_def, update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def]) >>
  qspecl_then [`tops`, `External`, `mut`, `fname`, `fargs`, `ret`, `fbody`,
               `use_trans`] strip_assume_tac build_compile_env_vars >>
  drule compile_register_positional_args_reserved >>
  impl_tac >- gvs[build_positional_args_FST] >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
  gvs[MEM_MAP] >> metis_tac[]
QED

(* The constructor's body likewise. *)
Theorem constructor_entry_locals:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   cenv0 pos_args rest dsz st cenv st'.
    package_constructor tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, fbody) =
      (cenv0, pos_args, rest) /\
    compile_register_constructor_args cenv0 pos_args 0 dsz st = (cenv, st') ==>
    local_ptrs_reserved cenv st' /\
    EVERY (\a. ?p sz. FLOOKUP cenv.ce_vars (FST a) = SOME (PtrVar (Var p) sz))
      fargs
Proof
  rpt gen_tac >> strip_tac >>
  `cenv0.ce_vars = (build_compile_env tops Deploy mut fname fargs ret fbody
                      use_trans).ce_vars /\
   pos_args = build_positional_args cenv0 fargs` by
    gvs[package_constructor_def, update_cenv_nonreentrant_def] >>
  qspecl_then [`tops`, `Deploy`, `mut`, `fname`, `fargs`, `ret`, `fbody`,
               `use_trans`] strip_assume_tac build_compile_env_vars >>
  drule compile_register_constructor_args_reserved >>
  impl_tac >- gvs[build_positional_args_FST] >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
  gvs[MEM_MAP] >> metis_tac[]
QED

(* The fallback has no parameters (supported_function_header_names), and
   its body is compiled in the env package_fallback_fn builds, which then
   holds no MemLoc variable and no pointer variable. *)
Theorem fallback_entry_locals:
  !tops use_trans nkey_map mut nr rr fname dflts ret fbody cenv rest st.
    package_fallback_fn tops use_trans nkey_map
      (SOME (mut, nr, rr, fname, [], dflts, ret, fbody)) =
      SOME (cenv, rest) ==>
    local_ptrs_reserved cenv st
Proof
  rpt gen_tac >> simp[package_fallback_fn_def] >> strip_tac >>
  qspecl_then [`tops`, `External`, `mut`, `fname`, `[]`, `ret`, `fbody`,
               `use_trans`] strip_assume_tac build_compile_env_vars >>
  gvs[local_ptrs_reserved_def] >> metis_tac[]
QED
