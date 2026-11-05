(* [simp] accessors for the event table of checked-contract environments. *)
Theory vyperTypeEventLookup
Ancestors
  vyperTypeContract vyperTypeEnvExtension vyperEvent finite_map list alist

Theorem function_entry_env_event_fields[simp]:
  (function_entry_env art mods src vis args).event_fields = art.cta_event_fields
Proof
  simp[function_entry_env_def] >>
  `!env. (FOLDL (\env (id,ty). extend_local env id ty (vis = Internal)) env args).event_fields =
          env.event_fields` suffices_by simp[artifact_env_def] >>
  Induct_on `args` >> simp[] >> Cases_on `h` >> simp[]
QED

Theorem artifact_env_event_fields[simp]:
  (artifact_env art mods src).event_fields = art.cta_event_fields
Proof
  simp[artifact_env_def]
QED

Theorem live_artifact_event_fields[simp]:
  (live_artifact layouts addr mods live art).cta_event_fields = art.cta_event_fields
Proof
  simp[live_artifact_def]
QED

