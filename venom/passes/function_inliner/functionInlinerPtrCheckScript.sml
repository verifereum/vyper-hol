Theory functionInlinerPtrCheck
Ancestors
  ptrOkCheck vyperCompiler ptrDiscipline pointerConfinedDefs memLocDefs
  venomInst venomExecSemantics list indexedLists option pred_set words

Definition inline_ptr_single_root_def:
  inline_ptr_single_root P func operand <=>
    case operand of
      Var v =>
        !r1 r2. r1 IN ptr_roots P func /\ r2 IN ptr_roots P func /\
                v IN pointer_derived_vars func {r1} /\
                v IN pointer_derived_vars func {r2} ==> r1 = r2
    | _ => T
End

Definition inline_ptr_ok_def:
  inline_ptr_ok P C <=>
    EVERY (\func.
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
        (FILTER (\i. i.inst_opcode = PARAM) (fn_insts func)))) /\
      EVERY (\inst.
        (case mem_write_ops inst of
           NONE => T
         | SOME ops => inline_ptr_single_root P func ops.iao_ofst) /\
        (inst.inst_opcode = INVOKE ==>
         case decode_invoke inst of
           NONE => F
         | SOME (nm, args) =>
             !k. k < LENGTH args ==>
                 (k IN P nm <=>
                   ?v. EL k args = Var v /\ v IN fn_pv P func) /\
                 (k IN P nm ==>
                  inline_ptr_single_root P func (EL k args))))
        (fn_insts func))
      C.ctx_functions
End

Definition inline_ptr_single_root_check_def:
  inline_ptr_single_root_check closures operand <=>
    case operand of
      Var v =>
        (case MAP FST (FILTER (\(_, vs). MEM v vs) closures) of
           [] => T
         | root::rest => EVERY ($= root) rest)
    | _ => T
End

Definition inline_fn_ptr_ok_check_def:
  inline_fn_ptr_ok_check PL func <=>
    let roots = opcode_root_list ALLOCA func ++ opcode_root_list DALLOCA func ++
                param_root_list (PL func.fn_name) func in
    case (pv_closure func roots,
          OPT_MMAP (\r. OPTION_MAP (\vs. (r,vs)) (pv_closure func [r]))
            roots) of
      (SOME pv, SOME closures) =>
        ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
          (FILTER (\i. i.inst_opcode = PARAM) (fn_insts func)))) /\
        EVERY (\inst.
          (case mem_write_ops inst of
             NONE => T
           | SOME ops => inline_ptr_single_root_check closures ops.iao_ofst) /\
          (inst.inst_opcode = INVOKE ==>
           case decode_invoke inst of
             NONE => F
           | SOME (nm, args) =>
               EVERY I (MAPi (\k arg.
                 (MEM k (PL nm) <=> case arg of Var v => MEM v pv | _ => F) /\
                 (MEM k (PL nm) ==>
                  inline_ptr_single_root_check closures arg)) args)))
          (fn_insts func)
    | _ => F
End

Definition inline_ptr_ok_check_def:
  inline_ptr_ok_check C <=>
    EVERY (inline_fn_ptr_ok_check (ctx_ptr_param_list C)) C.ctx_functions
End

Theorem inline_opcode_roots:
  MEM v (opcode_root_list op func) <=>
  ?i. MEM i (fn_insts func) /\ i.inst_opcode = op /\ inst_output i = SOME v
Proof
  simp[opcode_root_list_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  eq_tac >> rpt strip_tac >> rename1 `MEM inst (fn_insts func)`
  >- (Cases_on `inst.inst_opcode = op` >>
      Cases_on `inst_output inst` >> gvs[] >>
      qexists_tac `inst` >> simp[]) >>
  qexists_tac `inst` >> simp[]
QED

Theorem inline_param_roots[local]:
  !params func v.
    MEM v (param_root_list params func) <=>
    ?i k. MEM i (fn_insts func) /\ i.inst_opcode = PARAM /\
          i.inst_operands = [Lit k] /\ MEM (w2n k) params /\
          inst_output i = SOME v
Proof
  simp[param_root_list_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt gen_tac >> eq_tac >> rpt strip_tac >>
  rename1 `MEM inst (fn_insts func)`
  >- (Cases_on `inst.inst_opcode = PARAM` >> gvs[] >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      rename1 `inst.inst_operands = op1::rest` >>
      Cases_on `op1` >> Cases_on `rest` >> gvs[] >>
      Cases_on `inst_output inst` >> gvs[] >>
      rename1 `inst.inst_operands = [Lit idx]` >>
      qexistsl_tac [`inst`, `idx`] >> gvs[] >>
      Cases_on `MEM (w2n idx) params` >> gvs[]) >>
  qexists_tac `inst` >> simp[]
QED

Theorem inline_root_list_set:
  set (opcode_root_list ALLOCA func ++ opcode_root_list DALLOCA func ++
       param_root_list (PL func.fn_name) func) =
    ptr_roots (\nm. set (PL nm)) func
Proof
  rw[EXTENSION, ptr_roots_def, alloca_roots_def,
     inline_opcode_roots, inline_param_roots] >>
  metis_tac[]
QED

Theorem inline_opt_mmap_member[local]:
  !xs ys f x. OPT_MMAP f xs = SOME ys /\ MEM x xs ==>
              ?y. f x = SOME y /\ MEM y ys
Proof
  Induct >> simp[OPT_MMAP_def] >> rpt gen_tac >>
  Cases_on `f h` >> Cases_on `OPT_MMAP f xs` >> gvs[] >>
  strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `f x = SOME y` >> qexists_tac `y` >> simp[]
QED

Theorem inline_single_root_check_sound[local]:
  (!r. r IN ptr_roots P func ==>
       ?vs. MEM (r,vs) closures /\ pointer_derived_vars func {r} = set vs) /\
  inline_ptr_single_root_check closures operand ==>
  inline_ptr_single_root P func operand
Proof
  Cases_on `operand` >>
  gvs[inline_ptr_single_root_check_def, inline_ptr_single_root_def] >>
  rpt strip_tac >>
  rename1 `r1 = r2` >>
  rename1 `v IN pointer_derived_vars func {r1}` >>
  `?vs. MEM (r1,vs) closures /\ pointer_derived_vars func {r1} = set vs`
    by metis_tac[] >>
  `?ws. MEM (r2,ws) closures /\ pointer_derived_vars func {r2} = set ws`
    by metis_tac[] >>
  gvs[] >>
  `MEM r1 (MAP FST (FILTER (\(_, w). MEM v w) closures))` by
    (simp[MEM_MAP, MEM_FILTER] >> qexists_tac `(r1,vs)` >> simp[]) >>
  `MEM r2 (MAP FST (FILTER (\(_, w). MEM v w) closures))` by
    (simp[MEM_MAP, MEM_FILTER] >> qexists_tac `(r2,ws)` >> simp[]) >>
  Cases_on `MAP FST (FILTER (\(_, w). MEM v w) closures)` >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem inline_ptr_ok_check_sound:
  inline_ptr_ok_check C ==> inline_ptr_ok (\nm. set (ctx_ptr_param_list C nm)) C
Proof
  simp_tac std_ss [inline_ptr_ok_check_def, inline_ptr_ok_def, EVERY_MEM] >>
  strip_tac >> qx_gen_tac `func` >> strip_tac >>
  first_x_assum (drule_then mp_tac) >>
  simp_tac std_ss [inline_fn_ptr_ok_check_def, LET_THM] >>
  qabbrev_tac `PL = ctx_ptr_param_list C` >>
  qabbrev_tac `roots = opcode_root_list ALLOCA func ++
                      opcode_root_list DALLOCA func ++
                      param_root_list (PL func.fn_name) func` >>
  qabbrev_tac `close = \r. OPTION_MAP (\vs. (r,vs)) (pv_closure func [r])` >>
  Cases_on `pv_closure func roots` >> Cases_on `OPT_MMAP close roots` >>
  gvs[] >> strip_tac >>
  `set roots = ptr_roots (\nm. set (PL nm)) func` by
    simp[Abbr `roots`, inline_root_list_set] >>
  rename1 `pv_closure func roots = SOME pv` >>
  rename1 `OPT_MMAP close roots = SOME closures` >>
  `fn_pv (\nm. set (PL nm)) func = set pv` by
    metis_tac[fn_pv_def, pv_closure_set] >>
  `!r. r IN ptr_roots (\nm. set (PL nm)) func ==>
       ?vs. MEM (r,vs) closures /\ pointer_derived_vars func {r} = set vs` by
    (qx_gen_tac `r` >> strip_tac >>
     `MEM r roots` by
       (qpat_x_assum `set roots = _` (fn eq => fs[GSYM eq])) >>
     drule_all inline_opt_mmap_member >>
     Cases_on `pv_closure func [r]` >> simp[Abbr `close`] >>
     strip_tac >> metis_tac[pv_closure_set, listTheory.LIST_TO_SET_THM]) >>
  `!op. inline_ptr_single_root_check closures op ==>
        inline_ptr_single_root (\nm. set (PL nm)) func op` by
    metis_tac[inline_single_root_check_sound] >>
  qx_gen_tac `inst` >> strip_tac >>
  qpat_x_assum `EVERY _ (fn_insts func)` (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  disch_then (drule_then strip_assume_tac) >>
  conj_tac
  >- (Cases_on `mem_write_ops inst` >> gvs[] >> res_tac) >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME decoded` >>
  PairCases_on `decoded` >> gvs[] >>
  rename1 `decode_invoke inst = SOME (name,args)` >>
  qpat_x_assum `!e. MEM e (MAPi _ args) ==> e` mp_tac >>
  simp[MEM_MAPi, PULL_EXISTS] >>
  rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
  Cases_on `EL k args` >> gvs[] >> metis_tac[]
QED
