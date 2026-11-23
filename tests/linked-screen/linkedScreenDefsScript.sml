(* Executable forms of the linked-unit predicates the screen evaluates.
 *
 * Each predicate is defined with the text of the clause it screens
 * (contract_inv_def, linked_body_calls_resolved_def, layouts_agree_mods_def),
 * the contract's runtime context fixed to the screen's one deployment, and
 * gets a proved rewrite to a list-quantified form that EVAL decides.
 *
 * TOP-LEVEL: screen_layouts_agree, screen_g1 .. screen_g4 and their _exec
 * rewrites, screen_evm_run and screen_src_run (the deploy and one call).
 *)
Theory linkedScreenDefs
Ancestors
  bodyInvSplit bodyCallSupport bodyQualifiedStmtSupport e2eModsDefs
  e2eDeployModsDefs e2eWitnessCompute compileUnit vyperTypeContract
  supportedProgram supportedDecls supportedTypes vyperInterpreter
  vyperABI contractABI constSubstMods list alist pair rich_list
Libs
  cv_transLib

(* ===== Generic list forms of the quantified clauses ===== *)

Theorem alookup_forall_every:
  (!src tops. ALOOKUP mods src = SOME tops ==> P src tops) <=>
  EVERY (\(src,tops). ALOOKUP mods src = SOME tops ==> P src tops) mods
Proof
  simp[EVERY_MEM, FORALL_PROD] >> metis_tac[ALOOKUP_MEM]
QED

Definition screen_fn_decls_def:
  screen_fn_decls [] = [] /\
  screen_fn_decls (FunctionDecl vis mut nr rr name args dflts ret ss :: tls) =
    (vis,mut,nr,rr,name,args,dflts,ret,ss) :: screen_fn_decls tls /\
  screen_fn_decls (_ :: tls) = screen_fn_decls tls
End

Theorem MEM_screen_fn_decls:
  !tops. MEM (vis,mut,nr,rr,name,args,dflts,ret,ss) (screen_fn_decls tops) <=>
         MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops
Proof
  Induct >> simp[screen_fn_decls_def] >> Cases >> simp[screen_fn_decls_def]
QED

Theorem fn_forall_every:
  (!src tops vis mut nr rr name args dflts ret ss.
     ALOOKUP mods src = SOME tops /\
     MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
     A src tops vis mut nr rr name args dflts ret ss ==>
     B src tops vis mut nr rr name args dflts ret ss) <=>
  EVERY (\(src,tops). ALOOKUP mods src = SOME tops ==>
    EVERY (\(vis,mut,nr,rr,name,args,dflts,ret,ss).
      A src tops vis mut nr rr name args dflts ret ss ==>
      B src tops vis mut nr rr name args dflts ret ss)
      (screen_fn_decls tops)) mods
Proof
  simp[EVERY_MEM, FORALL_PROD, MEM_screen_fn_decls] >>
  metis_tac[ALOOKUP_MEM]
QED

(* ===== The screen's deployment context ===== *)

(* One contract at 2w; contract_inv reads the module list, layouts, mode
   and lock slot of the context only through these fields. *)
Definition screen_cx_def:
  screen_cx d lay mods =
    empty_evaluation_context with
      <| sources := [(2w, mods)]; txn := empty_call_txn with target := 2w;
         layouts := [(2w, lay)]; in_deploy := d;
         nonreentrant_slot := lookup_nonreentrant_slot [(2w : address, lay)] 2w |>
End

(* ===== (b) group 1: module headers and the main gate ===== *)

Definition screen_g1_def[nocompute]:
  screen_g1 d mods exps <=>
    IS_SOME (ALOOKUP mods NONE) /\
    ALL_DISTINCT (MAP FST mods) /\
    (!src tops. ALOOKUP mods src = SOME tops ==>
       supported_module_headers tops /\
       (src = NONE ==>
          supported_program tops /\
          (d ==> supported_program_deploy tops)) /\
       ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))) /\
    ALL_DISTINCT (FLAT (MAP (\(src,tops).
       FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) mods)) /\
    (d ==> IS_SOME (FST (SND (SND (SND (classify_functions_unit mods exps))))))
End

Theorem screen_g1_exec:
  screen_g1 d mods exps <=>
    IS_SOME (ALOOKUP mods NONE) /\
    ALL_DISTINCT (MAP FST mods) /\
    EVERY (\(src,tops). ALOOKUP mods src = SOME tops ==>
       supported_module_headers tops /\
       (src = NONE ==>
          supported_program tops /\
          (d ==> supported_program_deploy tops)) /\
       ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))) mods /\
    ALL_DISTINCT (FLAT (MAP (\(src,tops).
       FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) mods)) /\
    (d ==> IS_SOME (FST (SND (SND (SND (classify_functions_unit mods exps))))))
Proof
  simp[screen_g1_def, alookup_forall_every]
QED

(* ===== (b) group 2: live function bodies ===== *)

Definition screen_g2_def[nocompute]:
  screen_g2 d lay mods exps <=>
    let cx = screen_cx d lay mods in
    (!src tops vis mut nr rr name args dflts ret ss.
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
       (src = NONE \/ MEM (src,name) (linked_live_functions mods exps)) ==>
       function_mutability_ok mods vis mut nr dflts ss /\
       (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
       (cx.in_deploy /\ vis = Deploy ==> EVERY (supported_value_type tops o SND) args)) /\
    (!src tops vis mut nr rr name args dflts ret ss.
       ALOOKUP mods src = SOME tops /\
       MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
       (src = NONE \/ context_function_live cx (src,name)) ==>
       supported_declaration_body tops
         (FunctionDecl vis mut nr rr name args dflts ret ss) /\
       (cx.in_deploy ==> supported_deploy_declaration tops
         (FunctionDecl vis mut nr rr name args dflts ret ss)))
End

Theorem screen_g2_exec:
  screen_g2 d lay mods exps <=>
    let cx = screen_cx d lay mods in
    EVERY (\(src,tops). ALOOKUP mods src = SOME tops ==>
      EVERY (\(vis,mut,nr,rr,name,args,dflts,ret,ss).
        (src = NONE \/ MEM (src,name) (linked_live_functions mods exps)) ==>
        function_mutability_ok mods vis mut nr dflts ss /\
        (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
        (cx.in_deploy /\ vis = Deploy ==> EVERY (supported_value_type tops o SND) args))
      (screen_fn_decls tops)) mods /\
    EVERY (\(src,tops). ALOOKUP mods src = SOME tops ==>
      EVERY (\(vis,mut,nr,rr,name,args,dflts,ret,ss).
        (src = NONE \/ context_function_live cx (src,name)) ==>
        supported_declaration_body tops
          (FunctionDecl vis mut nr rr name args dflts ret ss) /\
        (cx.in_deploy ==> supported_deploy_declaration tops
          (FunctionDecl vis mut nr rr name args dflts ret ss)))
      (screen_fn_decls tops)) mods
Proof
  rewrite_tac[screen_g2_def, LET_THM] >> BETA_TAC >>
  Ho_Rewrite.REWRITE_TAC[fn_forall_every]
QED

(* ===== (b) group 3: linked call resolution ===== *)

Definition screen_g3_def[nocompute]:
  screen_g3 d lay mods <=> linked_body_calls_resolved mods (screen_cx d lay mods)
End

Definition screen_singleton_def:
  screen_singleton mods <=>
    case mods of [(NONE, _)] => T | _ => F
End

Theorem screen_singleton_eq:
  (!tops. mods <> [(NONE,tops)]) <=> ~screen_singleton mods
Proof
  simp[screen_singleton_def] >> BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem screen_g3_exec:
  screen_g3 d lay mods <=>
    let cx = screen_cx d lay mods in
    (~screen_singleton mods ==>
     EVERY (\(src,tops). ALOOKUP mods src = SOME tops ==>
       EVERY (\(vis,mut,nr,raw,name,args,dflts,ret,ss).
         context_function_live cx (src,name) /\
         check_function_body_in_mode cx.in_deploy vis ==>
         EVERY (\call. case ALOOKUP mods (FST call) of
                         NONE => F
                       | SOME target_tops =>
                           supported_linked_callee cx.in_deploy target_tops call)
           (function_int_calls dflts ss))
         (screen_fn_decls tops)) mods)
Proof
  `!P k. (?t. ALOOKUP mods k = SOME t /\ P t) <=>
         (case ALOOKUP mods k of NONE => F | SOME t => P t)` by
    (rpt gen_tac >> CASE_TAC >> simp[]) >>
  rewrite_tac[screen_g3_def, linked_body_calls_resolved_def, screen_singleton_eq,
              LET_THM] >> BETA_TAC >>
  Ho_Rewrite.REWRITE_TAC[fn_forall_every] >>
  pop_assum (fn th => Ho_Rewrite.REWRITE_TAC[th])
QED

(* ===== (b) group 4: qualified statements before and after inlining ===== *)

(* The statement-level gate with the existential of the Log case decided. *)
Definition screen_qualified_stmt_def:
  screen_qualified_stmt mods (Raise (RaiseCustomError err)) =
    qualified_custom_error_ok mods err /\
  screen_qualified_stmt mods (Assert e (AssertCustomError err)) =
    qualified_custom_error_ok mods err /\
  screen_qualified_stmt mods (Log id args) =
    (FST id = NONE \/
     case ALOOKUP mods (FST id) of
       NONE => F
     | SOME tops =>
         case supported_event_fields tops (NONE,SND id) of
           NONE => F
         | SOME fields =>
             LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e))
               args fields) /\
  screen_qualified_stmt mods (If e yes no) =
    (screen_qualified_stmts mods yes /\ screen_qualified_stmts mods no) /\
  screen_qualified_stmt mods (For id ty it n body) =
    screen_qualified_stmts mods body /\
  screen_qualified_stmt mods _ = T /\
  screen_qualified_stmts mods [] = T /\
  screen_qualified_stmts mods (s::ss) =
    (screen_qualified_stmt mods s /\ screen_qualified_stmts mods ss)
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,s) => stmt_size s | INR (_,ss) => list_size stmt_size ss)` >>
  simp[]
End

Theorem screen_qualified_stmts_eq:
  (!mods s. screen_qualified_stmt mods s <=> qualified_stmt_decls_ok mods s) /\
  (!mods ss. screen_qualified_stmts mods ss <=> qualified_stmts_decls_ok mods ss)
Proof
  ho_match_mp_tac screen_qualified_stmt_ind >>
  rw[screen_qualified_stmt_def, qualified_stmt_decls_ok_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

(* Over the bodies linked_body_calls_resolved examines. *)
Definition screen_g4_def[nocompute]:
  screen_g4 d lay mods <=>
    let cx = screen_cx d lay mods in
    !src tops vis mut nr raw name args dflts ret ss.
      ALOOKUP mods src = SOME tops /\
      MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
      context_function_live cx (src,name) /\
      check_function_body_in_mode cx.in_deploy vis ==>
      qualified_stmts_decls_ok mods ss /\
      qualified_stmts_decls_ok mods
        (subst_consts_stmts_mods (consts_env_mods mods) ss)
End

Theorem screen_g4_exec:
  screen_g4 d lay mods <=>
    let cx = screen_cx d lay mods in
    EVERY (\(src,tops). ALOOKUP mods src = SOME tops ==>
      EVERY (\(vis,mut,nr,raw,name,args,dflts,ret,ss).
        context_function_live cx (src,name) /\
        check_function_body_in_mode cx.in_deploy vis ==>
        screen_qualified_stmts mods ss /\
        screen_qualified_stmts mods
          (subst_consts_stmts_mods (consts_env_mods mods) ss))
        (screen_fn_decls tops)) mods
Proof
  rewrite_tac[screen_g4_def, LET_THM, GSYM (CONJUNCT2 screen_qualified_stmts_eq)] >>
  BETA_TAC >> Ho_Rewrite.REWRITE_TAC[fn_forall_every]
QED

(* ===== (a): layouts_agree_mods on the screen's machine ===== *)

(* The immutable regions, with the declaration's prefix carried along. *)
Definition screen_imm_regions_def:
  screen_imm_regions sf single src pre [] = [] /\
  screen_imm_regions sf single src pre (tl :: rest) =
    (case tl of
       VariableDecl vis Immutable name ty slot =>
         (if single then [(src, name, compute_immutables_len sf pre,
                           type_mem_bytes sf ty)]
          else case slot of
                 NONE => []
               | SOME off => [(src, name, off, type_mem_bytes sf ty)])
     | _ => []) ++
    screen_imm_regions sf single src (pre ++ [tl]) rest
End

Theorem MEM_screen_imm_regions:
  !rest pre.
    MEM (src', name, off, sz) (screen_imm_regions sf single src pre rest) <=>
    src' = src /\
    ?p post vis ty slot.
      rest = p ++ VariableDecl vis Immutable name ty slot :: post /\
      (if single then off = compute_immutables_len sf (pre ++ p)
       else slot = SOME off) /\
      sz = type_mem_bytes sf ty
Proof
  Induct >- simp[screen_imm_regions_def] >> rpt gen_tac >>
  `!h. (?p post vis ty slot.
          h::rest = p ++ VariableDecl vis Immutable name ty slot :: post /\
          (if single then off = compute_immutables_len sf (pre ++ p)
           else slot = SOME off) /\
          sz = type_mem_bytes sf ty) <=>
       (?vis ty slot. h = VariableDecl vis Immutable name ty slot /\
          (if single then off = compute_immutables_len sf pre
           else slot = SOME off) /\
          sz = type_mem_bytes sf ty) \/
       (?p post vis ty slot.
          rest = p ++ VariableDecl vis Immutable name ty slot :: post /\
          (if single then off = compute_immutables_len sf ((pre ++ [h]) ++ p)
           else slot = SOME off) /\
          sz = type_mem_bytes sf ty)` by
    (gen_tac >> eq_tac >> strip_tac
     >- (Cases_on `p` >> gvs[] >> metis_tac[APPEND_ASSOC, APPEND])
     >- (qexistsl [`[]`, `rest`] >> simp[])
     >> qexists_tac `h::p` >> gvs[] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  pop_assum (fn th => rewrite_tac[th, screen_imm_regions_def, MEM_APPEND]) >>
  first_x_assum (fn ih => rewrite_tac[ih]) >>
  Cases_on `h` >> simp[] >>
  rename1 `VariableDecl vv mm nn tt ss` >> Cases_on `mm` >> simp[] >>
  Cases_on `single` >> simp[] >> Cases_on `ss` >> simp[] >> metis_tac[]
QED

Definition screen_regions_def:
  screen_regions mods =
    let sf = get_struct_fields (make_struct_fields_map_mods mods) in
    FLAT (MAP (\(src,tops).
      if ALOOKUP mods src = SOME tops
      then screen_imm_regions sf (mods = [(NONE,tops)]) src [] tops
      else []) mods)
End

Theorem screen_regions_mem:
  immutable_region_mods mods src name off sz <=>
  MEM (src, name, off, sz) (screen_regions mods)
Proof
  simp[immutable_region_mods_def, screen_regions_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS, EXISTS_PROD] >>
  eq_tac >> strip_tac
  >- (drule ALOOKUP_MEM >> strip_tac >> first_assum (irule_at Any) >>
      gvs[MEM_screen_imm_regions] >> qexistsl [`pre`, `post`] >> simp[])
  >> rename1 `ALOOKUP mods src0 = SOME tops0` >>
  Cases_on `ALOOKUP mods src0 = SOME tops0` >> gvs[MEM_screen_imm_regions] >>
  qexistsl [`p`, `post`, `vis`, `ty`, `slot`] >> gvs[]
QED

Definition screen_layouts_agree_def[nocompute]:
  screen_layouts_agree mods exps lay <=>
    layouts_agree_mods mods exps
      (initial_machine_state with layouts := [(2w, lay)])
      (empty_call_txn with target := 2w)
End

Definition screen_slots_agree_def:
  screen_slots_agree mods exps sl tl <=>
    EVERY (\(src,tops). EVERY (\tl'. case tl' of
        VariableDecl vis Storage id ty slot_opt => ALOOKUP sl (src, id) = slot_opt
      | VariableDecl vis Transient id ty slot_opt => ALOOKUP tl (src, id) = slot_opt
      | HashMapDecl vis tr id kt vt slot_opt =>
          ALOOKUP (if tr then tl else sl) (src, id) = slot_opt
      | FunctionDecl vis mut nr rr name args dflts ret fbody =>
          (nr /\ (src = NONE \/ MEM (src, name) (linked_live_functions mods exps)) ==>
           ALOOKUP tl (NONE, "$.nonreentrant_key") = SOME global_nonreentrant_slot)
      | _ => T) tops) mods
End

Theorem screen_slots_agree_eq:
  screen_slots_agree mods exps sl tl <=>
    !src tops. MEM (src, tops) mods ==>
      (!vis id ty slot_opt. MEM (VariableDecl vis Storage id ty slot_opt) tops ==>
                            ALOOKUP sl (src, id) = slot_opt) /\
      (!vis id ty slot_opt. MEM (VariableDecl vis Transient id ty slot_opt) tops ==>
                            ALOOKUP tl (src, id) = slot_opt) /\
      (!vis tr id kt vt slot_opt. MEM (HashMapDecl vis tr id kt vt slot_opt) tops ==>
                                  ALOOKUP (if tr then tl else sl) (src, id) = slot_opt) /\
      (!vis mut rr name args dflts ret fbody.
         MEM (FunctionDecl vis mut T rr name args dflts ret fbody) tops /\
         (src = NONE \/ MEM (src, name) (linked_live_functions mods exps)) ==>
         ALOOKUP tl (NONE, "$.nonreentrant_key") = SOME global_nonreentrant_slot)
Proof
  simp[screen_slots_agree_def, EVERY_MEM, FORALL_PROD] >>
  eq_tac
  >- (rpt strip_tac >> first_x_assum drule >> disch_then drule >> fs[])
  >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  Cases_on `tl'` >> simp[] >>
  rpt CASE_TAC >> rpt strip_tac >> gvs[] >> res_tac >> fs[]
QED

Theorem screen_layouts_agree_exec:
  screen_layouts_agree mods exps (sl, tl) <=>
    EVERY (\(src,name,off,sz). off + sz <= imm_len_mods mods)
      (screen_regions mods) /\
    EVERY (\(src,name,off,sz). EVERY (\(src',name',off',sz').
       (src,name) <> (src',name') ==>
       loweringStateRelDefs$regions_disjoint off sz off' sz')
       (screen_regions mods)) (screen_regions mods) /\
    EVERY (\i. EXISTS (\(src,name,off,sz). off <= i /\ i < off + sz)
                 (screen_regions mods))
      (COUNT_LIST (imm_len_mods mods)) /\
    screen_slots_agree mods exps sl tl
Proof
  simp[screen_layouts_agree_def, layouts_agree_mods_def, screen_regions_mem,
       screen_slots_agree_eq, EVERY_MEM, FORALL_PROD, MEM_COUNT_LIST,
       EXISTS_MEM, EXISTS_PROD] >>
  metis_tac[]
QED

(* ===== (c): the deployment and one call, on both sides ===== *)

Definition screen_deploy_tx_def:
  screen_deploy_tx (bc : word8 list) = empty_call_txn with
    <| target := 2w; sender := 1w; function_name := "__init__";
       code := bc; created_in_tx := T;
       block_number := 1; block_hashes := [0w] |>
End

Definition screen_call_tx_def:
  screen_call_tx fname (data : word8 list) (code : word8 list) =
    empty_call_txn with
    <| target := 2w; sender := 1w; function_name := fname;
       calldata := data; code := code;
       block_number := 1; block_hashes := [0w] |>
End

Definition screen_es_dep_def:
  screen_es_dep bc =
    <| contexts := [(p23_frame bc [] (Code 2w), p23_dep_rollback)];
       txParams := p23_tx_params; rollback := p23_dep_rollback;
       originalAccounts := empty_accounts;
       msdomain := Collect empty_domain |>
End

Definition screen_es_call_def:
  screen_es_call accts data =
    let rb = p23_dep_rollback with accounts := accts in
      <| contexts :=
           [(p23_frame (lookup_account 2w accts).code data
               (Memory <| offset := 0; size := 0 |>), rb)];
         txParams := p23_tx_params; rollback := rb;
         originalAccounts := accts;
         msdomain := Collect empty_domain |>
End

Definition screen_slots_def:
  screen_slots accts (ks : num list) =
    MAP (\k. lookup_storage (n2w k) (lookup_account 2w accts).storage) ks
End

Definition screen_return_data_def:
  screen_return_data es =
    case es.contexts of
      [] => []
    | (c, _) :: _ => c.returnData
End

(* The bytes a source outcome stands for: a returned value's canonical
   encoding, or revert data; NONE where no byte-level comparison applies. *)
Definition screen_src_bytes_def:
  screen_src_bytes tenv ret res =
    case res of
      INL v =>
        if ret = NoneT then SOME [] else
        (case vyper_to_abi tenv ret v of
           NONE => NONE
         | SOME abi_v =>
             SOME (if needs_external_call_wrap ret
                   then enc (Tuple [vyper_to_abi_type tenv ret]) (ListV [abi_v])
                   else enc (vyper_to_abi_type tenv ret) abi_v))
    | INR (Error (RevertData bs)) => SOME bs
    | INR _ => NONE
End

Definition screen_src_ok_def:
  screen_src_ok res <=>
    case res of INL _ => T | INR HaltException => T | _ => F
End

(* Deploy and call on the EVM: NONE if a run doesn't end; else whether
   deployment succeeded, the storage slots after it, the installed code,
   and the call's success, return data and slots. *)
Definition screen_evm_run_def:
  screen_evm_run dbc data ks =
    case run_call (screen_es_dep dbc) of
      NONE => NONE
    | SOME (r, es') =>
        if r <> INR NONE then SOME (F, [], [], F, [], []) else
        let accts = process_deletions es'.rollback.toDelete es'.rollback.accounts in
        case run_call (screen_es_call accts data) of
          NONE => NONE
        | SOME (r2, es'') =>
            let accts2 = process_deletions es''.rollback.toDelete
                           es''.rollback.accounts in
            SOME (T, screen_slots accts ks, (lookup_account 2w accts).code,
                  r2 = INR NONE, screen_return_data es'',
                  screen_slots accts2 ks)
End

(* The same on the interpreter: the call starts from the deployed source
   machine, with the EVM's installed code as the transaction's code. *)
Definition screen_src_run_def:
  screen_src_run lay mods exps dbc fname data code ret ks =
    case load_contract (SOME []) []
           (initial_machine_state with layouts := [(2w, lay)])
           (screen_deploy_tx dbc) mods exps of
      INR _ => (F, [], F, NONE, [])
    | INL (am, _) =>
        let am1 = am with <| tStorage := empty_transient_storage; logs := [];
                             pending_deletions := [] |> in
        case call_external (SOME []) [] am1 (screen_call_tx fname data code) of
          (res, am2, _) =>
            (T, screen_slots am.accounts ks, screen_src_ok res,
             screen_src_bytes (type_env_all_modules mods) ret res,
             screen_slots am2.accounts ks)
End

val () = cv_auto_trans screen_deploy_tx_def;
val () = cv_auto_trans screen_call_tx_def;
val () = cv_auto_trans screen_es_dep_def;
val () = cv_auto_trans screen_es_call_def;
val () = cv_auto_trans screen_slots_def;
val () = cv_auto_trans screen_return_data_def;
val () = cv_auto_trans screen_src_bytes_def;
val () = cv_auto_trans screen_src_ok_def;
val () = cv_auto_trans screen_evm_run_def;
val () = cv_auto_trans screen_src_run_def;
