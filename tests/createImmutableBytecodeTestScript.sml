(* Immutable initcode must be copied from its declared region before CREATE. *)
Theory createImmutableBytecodeTest
Ancestors
  exprLowering exprLoweringProps vyperCompiler venomCallOracleDefs
  venomExecSemantics venomState compileEnv context words list
  vyperState valueEncoding loweringStateRelDefs
Libs
  wordsLib

Definition immutable_snapshot_request_ok_def:
  immutable_snapshot_request_ok ctor =
    let cenv = (ARB:compile_env) with
      <|ce_is_ctor := ctor; ce_imm_alloca := SOME (Lit 256w)|> in
    let vv = LocatedValue (BaseT (BytesT (Dynamic 10)))
      (mk_ptr (Lit 0w) LocCode) in
    let cs = initial_compile_state "entry" in
    let (ptr, compiled) = compile_create_snapshot cenv vv
      (BaseT (BytesT (Dynamic 49152))) cs in
    let bytes = REPLICATE 31 0w ++ [2w;96w;0w] ++ REPLICATE 30 0w in
    let initial = (init_venom_state "entry") with
      <|vs_alloca_next := 1024;
        vs_memory := if ctor then REPLICATE 256 0w ++ bytes else [];
        vs_data_section := if ctor then [] else bytes|> in
    case run_inst_seq (emitted_insts cs compiled) initial of
      OK post =>
        eval_operand ptr post = SOME 1024w /\
        mload 1024 post = 2w /\
        (venom_create_request post 0w 1056w (mload 1024 post) NONE).cr_data =
          [96w;0w] /\
        LENGTH post.vs_memory = 1088 /\
        post.vs_alloca_next = 50208
    | _ => F
End

Theorem immutable_creation_snapshot_request:
  immutable_snapshot_request_ok F /\ immutable_snapshot_request_ok T
Proof
  EVAL_TAC
QED

(* A live borrowed local needs no tracked allocation.  The same initialized
   constructor immutable admits [64,96), but rejects a local alias at zero. *)
Theorem immutable_alloca_sep_borrowed_witness:
  !func ce cx es s entry c v t u.
    (c,v,t,u) =
      (ce with <| ce_is_ctor := T; ce_module := NONE; ce_module_var_type := K NONE;
          ce_module_vars := FEMPTY |+ ((NONE,"imm"), ImmutableLoc 0);
          ce_vars := FEMPTY |+ ("local", PtrVar (Var "p") 32) |>,
       es with <| scopes := [FEMPTY |+ ("local",entry)];
          immutables := [(cx.txn.target,
            [(NONE,FEMPTY |+ ("imm",(BaseTV BoolT,BoolV T)))])] |>,
       s with <| vs_allocas := FEMPTY; vs_alloca_next := 96;
                 vs_vars := FEMPTY |+ ("p",64w) |>,
       s with <| vs_allocas := FEMPTY; vs_alloca_next := 96;
                 vs_vars := FEMPTY |+ ("p",0w) |>) ==>
      local_region c v.scopes t "local" 64 32 /\
      t.vs_allocas = FEMPTY /\
      immutable_alloca_sep func c cx v t /\
      local_region c v.scopes u "local" 0 32 /\
      ~immutable_alloca_sep func c cx v u
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[local_region_def, lookup_scopes_def, lookup_var_def,
       immutable_alloca_sep_def, immutable_decl_sep_alt, get_source_immutables_def,
       finite_mapTheory.FLOOKUP_UPDATE, nsid_to_string_def,
       type_memory_size_def, loweringStateRelDefsTheory.regions_disjoint_def, wordsTheory.dimword_def,
       venomMemPropsTheory.dimindex_256] >>
  conj_tac
  >- (rpt strip_tac >> gvs[AllCaseEqs()] >>
      Cases_on `id = "local"` >> gvs[]) >>
  qexistsl_tac [`"local"`, `0`, `32`] >> simp[]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createImmutableBytecodeTest");
