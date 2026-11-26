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

(* Each pointer PARAM of func that the operand derives from is at a
   write-reaching position W of func. *)
Definition inline_param_reach_ok_def:
  inline_param_reach_ok P W func operand <=>
    case operand of
      Var v =>
        !inst idx x.
          MEM inst (fn_insts func) /\ inst.inst_opcode = PARAM /\
          inst.inst_operands = [Lit idx] /\ w2n idx IN P func.fn_name /\
          inst_output inst = SOME x /\ v IN pointer_derived_vars func {x} ==>
          w2n idx IN W func.fn_name
    | _ => T
End

(* P holds the pointer parameter positions, W those a write can reach.
   A single root is asked only of write addresses and of arguments at
   write-reaching positions, and the PARAMs these derive from are
   write-reaching themselves. *)
Definition inline_ptr_ok_def:
  inline_ptr_ok P W C <=>
    EVERY (\func.
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
        (FILTER (\i. i.inst_opcode = PARAM) (fn_insts func)))) /\
      EVERY (\inst.
        (case mem_write_ops inst of
           NONE => T
         | SOME ops => inline_ptr_single_root P func ops.iao_ofst /\
                       inline_param_reach_ok P W func ops.iao_ofst) /\
        (inst.inst_opcode = INVOKE ==>
         case decode_invoke inst of
           NONE => F
         | SOME (nm, args) =>
             !k. k < LENGTH args ==>
                 (k IN P nm <=>
                   ?v. EL k args = Var v /\ v IN fn_pv P func) /\
                 (k IN W nm ==>
                  inline_ptr_single_root P func (EL k args) /\
                  inline_param_reach_ok P W func (EL k args))))
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

(* The positions and outputs of fn's PARAMs at the positions pl. *)
Definition param_root_idx_list_def:
  param_root_idx_list (pl : num list) fn =
    FLAT (MAP (\inst. if inst.inst_opcode = PARAM then
                        case (inst.inst_operands, inst_output inst) of
                          ([Lit idx], SOME out) =>
                            if MEM (w2n idx) pl then [(w2n idx, out)] else []
                        | _ => []
                      else [])
              (fn_insts fn))
End

Definition inline_param_reach_check_def:
  inline_param_reach_check pclosures wl operand <=>
    case operand of
      Var v => EVERY (\(j, vs). MEM v vs ==> MEM j wl) pclosures
    | _ => T
End

Definition inline_fn_ptr_ok_check_def:
  inline_fn_ptr_ok_check PL WL func <=>
    let roots = opcode_root_list ALLOCA func ++ opcode_root_list DALLOCA func ++
                param_root_list (PL func.fn_name) func in
    case (pv_closure func roots,
          OPT_MMAP (\r. OPTION_MAP (\vs. (r,vs)) (pv_closure func [r]))
            roots,
          OPT_MMAP (\(j,r). OPTION_MAP (\vs. (j,vs)) (pv_closure func [r]))
            (param_root_idx_list (PL func.fn_name) func)) of
      (SOME pv, SOME closures, SOME pclosures) =>
        ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
          (FILTER (\i. i.inst_opcode = PARAM) (fn_insts func)))) /\
        EVERY (\inst.
          (case mem_write_ops inst of
             NONE => T
           | SOME ops =>
               inline_ptr_single_root_check closures ops.iao_ofst /\
               inline_param_reach_check pclosures (WL func.fn_name)
                 ops.iao_ofst) /\
          (inst.inst_opcode = INVOKE ==>
           case decode_invoke inst of
             NONE => F
           | SOME (nm, args) =>
               EVERY I (MAPi (\k arg.
                 (MEM k (PL nm) <=> case arg of Var v => MEM v pv | _ => F) /\
                 (MEM k (WL nm) ==>
                  inline_ptr_single_root_check closures arg /\
                  inline_param_reach_check pclosures (WL func.fn_name) arg))
                 args)))
          (fn_insts func)
    | _ => F
End

Definition inline_ptr_ok_check_with_def:
  inline_ptr_ok_check_with WL C <=>
    EVERY (inline_fn_ptr_ok_check (ctx_ptr_param_list C) WL) C.ctx_functions
End

(* ===== Write-reaching positions ===== *)

(* The pointer parameter positions of func whose PARAM reaches a write
   address or an argument at a write-reaching position of its callee. *)
Definition write_reach_params_def:
  write_reach_params pl WL func =
    MAP FST (FILTER (\(j, x).
      case pv_closure func [x] of
        NONE => T
      | SOME vs =>
          EXISTS (\inst.
            (case mem_write_ops inst of
               SOME ops => (case ops.iao_ofst of Var v => MEM v vs | _ => F)
             | NONE => F) \/
            (inst.inst_opcode = INVOKE /\
             case decode_invoke inst of
               SOME (nm, args) =>
                 EXISTS I (MAPi (\k arg. MEM k (WL nm) /\
                   case arg of Var v => MEM v vs | _ => F) args)
             | NONE => F))
            (fn_insts func))
      (param_root_idx_list pl func))
End

Definition write_params_step_def:
  write_params_step C L =
    MAP (\func. (func.fn_name,
                 write_reach_params (ctx_ptr_param_list C func.fn_name)
                   (\nm. case ALOOKUP L nm of SOME l => l | NONE => [])
                   func))
      C.ctx_functions
End

(* One round per function reaches the fixed point on an acyclic call graph;
   the check below does not rely on it. *)
Definition ctx_write_params_def:
  ctx_write_params C nm =
    case ALOOKUP (FUNPOW (write_params_step C) (LENGTH C.ctx_functions) [])
           nm of
      SOME l => l
    | NONE => []
End

Definition ctx_write_param_set_def:
  ctx_write_param_set C nm =
    set (ctx_write_params C nm) INTER set (ctx_ptr_param_list C nm)
End

Definition inline_ptr_ok_check_def:
  inline_ptr_ok_check C <=> inline_ptr_ok_check_with (ctx_write_params C) C
End

(* Restates the first conjunct of ptrOkCheck's local ptr_roots_lists;
   it goes away when that theory exports it. *)
Theorem inline_root_list_set:
  set (opcode_root_list ALLOCA func ++ opcode_root_list DALLOCA func ++
       param_root_list (PL func.fn_name) func) =
    ptr_roots (\nm. set (PL nm)) func
Proof
  `!op v. MEM v (opcode_root_list op func) <=>
          ?i. MEM i (fn_insts func) /\ i.inst_opcode = op /\
              inst_output i = SOME v` by
    (simp[opcode_root_list_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     rpt gen_tac >> eq_tac >> rpt strip_tac >>
     rename1 `MEM inst (fn_insts func)`
     >- (Cases_on `inst.inst_opcode = op` >>
         Cases_on `inst_output inst` >> gvs[] >>
         qexists_tac `inst` >> simp[]) >>
     qexists_tac `inst` >> simp[]) >>
  `!params v. MEM v (param_root_list params func) <=>
              ?i k. MEM i (fn_insts func) /\ i.inst_opcode = PARAM /\
                    i.inst_operands = [Lit k] /\ MEM (w2n k) params /\
                    inst_output i = SOME v` by
    (simp[param_root_list_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
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
     qexists_tac `inst` >> simp[]) >>
  asm_simp_tac std_ss [EXTENSION, ptr_roots_def, alloca_roots_def,
                       MEM_APPEND, IN_UNION, IN_DIFF, GSPECIFICATION] >>
  metis_tac[]
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

Theorem inline_param_idx_roots[local]:
  !params func j x.
    MEM (j,x) (param_root_idx_list params func) <=>
    ?i k. MEM i (fn_insts func) /\ i.inst_opcode = PARAM /\
          i.inst_operands = [Lit k] /\ MEM (w2n k) params /\
          inst_output i = SOME x /\ j = w2n k
Proof
  simp[param_root_idx_list_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt gen_tac >> eq_tac >> rpt strip_tac >>
  rename1 `MEM inst (fn_insts func)`
  >- (Cases_on `inst.inst_opcode = PARAM` >> gvs[] >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      rename1 `inst.inst_operands = op1::rest` >>
      Cases_on `op1` >> Cases_on `rest` >> gvs[] >>
      Cases_on `inst_output inst` >> gvs[] >>
      rename1 `inst.inst_operands = [Lit idx]` >>
      Cases_on `MEM (w2n idx) params` >> gvs[] >>
      qexists_tac `inst` >> gvs[]) >>
  qexists_tac `inst` >> simp[]
QED

Theorem inline_param_reach_check_sound[local]:
  (!j x. MEM (j,x) (param_root_idx_list (PL func.fn_name) func) ==>
         ?vs. MEM (j,vs) pclosures /\ pointer_derived_vars func {x} = set vs) /\
  inline_param_reach_check pclosures (WL func.fn_name) operand ==>
  inline_param_reach_ok (\nm. set (PL nm))
    (\nm. set (WL nm) INTER set (PL nm)) func operand
Proof
  Cases_on `operand` >>
  simp[inline_param_reach_check_def, inline_param_reach_ok_def,
       EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> rename1 `inst_output inst = SOME x` >>
  `MEM (w2n idx, x) (param_root_idx_list (PL func.fn_name) func)` by
    (simp[inline_param_idx_roots] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem inline_ptr_ok_check_with_sound:
  inline_ptr_ok_check_with WL C ==>
  inline_ptr_ok (\nm. set (ctx_ptr_param_list C nm))
    (\nm. set (WL nm) INTER set (ctx_ptr_param_list C nm)) C
Proof
  simp_tac std_ss [inline_ptr_ok_check_with_def, inline_ptr_ok_def,
                   EVERY_MEM] >>
  strip_tac >> qx_gen_tac `func` >> strip_tac >>
  first_x_assum (drule_then mp_tac) >>
  simp_tac std_ss [inline_fn_ptr_ok_check_def, LET_THM] >>
  qabbrev_tac `PL = ctx_ptr_param_list C` >>
  qabbrev_tac `roots = opcode_root_list ALLOCA func ++
                      opcode_root_list DALLOCA func ++
                      param_root_list (PL func.fn_name) func` >>
  qabbrev_tac `close = \r. OPTION_MAP (\vs. (r,vs)) (pv_closure func [r])` >>
  qabbrev_tac `pclose = \(j,r). OPTION_MAP (\vs. (j:num,vs))
                                  (pv_closure func [r])` >>
  qabbrev_tac `pidx = param_root_idx_list (PL func.fn_name) func` >>
  Cases_on `pv_closure func roots` >> Cases_on `OPT_MMAP close roots` >>
  Cases_on `OPT_MMAP pclose pidx` >>
  gvs[] >> strip_tac >>
  `set roots = ptr_roots (\nm. set (PL nm)) func` by
    simp[Abbr `roots`, inline_root_list_set] >>
  rename1 `pv_closure func roots = SOME pv` >>
  rename1 `OPT_MMAP close roots = SOME closures` >>
  rename1 `OPT_MMAP pclose pidx = SOME pclosures` >>
  `fn_pv (\nm. set (PL nm)) func = set pv` by
    metis_tac[fn_pv_def, pv_closure_set] >>
  `!r. r IN ptr_roots (\nm. set (PL nm)) func ==>
       ?vs. MEM (r,vs) closures /\ pointer_derived_vars func {r} = set vs` by
    (qx_gen_tac `r` >> strip_tac >>
     `MEM r roots` by
       (qpat_x_assum `set roots = _` (fn eq => fs[GSYM eq])) >>
     `?y. close r = SOME y /\ MEM y closures` by
       (qpat_x_assum `OPT_MMAP close _ = _` mp_tac >>
        simp[vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
        rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
        first_x_assum drule >> strip_tac >> gvs[] >>
        qexists_tac `r` >> simp[]) >>
     Cases_on `pv_closure func [r]` >> gvs[Abbr `close`] >>
     metis_tac[pv_closure_set, listTheory.LIST_TO_SET_THM]) >>
  `!j x. MEM (j,x) pidx ==>
         ?vs. MEM (j,vs) pclosures /\ pointer_derived_vars func {x} = set vs` by
    (rpt strip_tac >>
     `?y. pclose (j,x) = SOME y /\ MEM y pclosures` by
       (qpat_x_assum `OPT_MMAP pclose _ = _` mp_tac >>
        simp[vyperMiscTheory.OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
        rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
        first_x_assum drule >> strip_tac >> gvs[] >>
        qexists_tac `(j,x)` >> simp[]) >>
     Cases_on `pv_closure func [x]` >> gvs[Abbr `pclose`] >>
     metis_tac[pv_closure_set, listTheory.LIST_TO_SET_THM]) >>
  `!op. inline_ptr_single_root_check closures op ==>
        inline_ptr_single_root (\nm. set (PL nm)) func op` by
    metis_tac[inline_single_root_check_sound] >>
  `!op. inline_param_reach_check pclosures (WL func.fn_name) op ==>
        inline_param_reach_ok (\nm. set (PL nm))
          (\nm. set (WL nm) INTER set (PL nm)) func op` by
    (rpt strip_tac >> irule inline_param_reach_check_sound >>
     qexists_tac `pclosures` >> fs[Abbr `pidx`]) >>
  qx_gen_tac `inst` >> strip_tac >>
  qpat_x_assum `EVERY _ (fn_insts func)` (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  disch_then (drule_then strip_assume_tac) >>
  conj_tac
  >- (Cases_on `mem_write_ops inst` >> gvs[]) >>
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

Theorem inline_ptr_ok_check_sound:
  inline_ptr_ok_check C ==>
  inline_ptr_ok (\nm. set (ctx_ptr_param_list C nm)) (ctx_write_param_set C) C
Proof
  strip_tac >> fs[inline_ptr_ok_check_def] >>
  drule inline_ptr_ok_check_with_sound >>
  `ctx_write_param_set C =
     (\nm. set (ctx_write_params C nm) INTER set (ctx_ptr_param_list C nm))` by
    simp[FUN_EQ_THM, ctx_write_param_set_def] >>
  simp[]
QED

Theorem ctx_write_param_set_subset:
  ctx_write_param_set C nm SUBSET set (ctx_ptr_param_list C nm)
Proof
  simp[ctx_write_param_set_def]
QED
