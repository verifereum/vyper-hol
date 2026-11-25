# Compiler correctness statement dossiers

The main dossier shows the single-module deployment and call correctness
and gas sufficiency theorems. A separate dossier shows the open
`vyper_call_correct_mods` target. Each page contains the statements,
hypothesis explanations and a linked definition index.

From a vyper-hol Git checkout, with `holbuild`, Python 3.10 or later and
`pandoc` on `PATH`, run:

```sh
python3 tools/statement-dossier/render.py --output /path/to/compiler-correctness.html
```

To generate the target dossier, supply the signed draft's Git revision
and path. The checkout must have the draft commit available locally.
Use the draft revision for the review round, or read it from the source
line of the page you are regenerating.

```sh
python3 tools/statement-dossier/render.py \
  --draft "$draft_revision:lowering/e2eModsTopsDraftScript.sml" \
  --output /path/to/module-list-target.html
```

Use an existing output directory and open the resulting standalone HTML
file in a browser. Use the same vyper-hol commit and draft commit to
regenerate a page. Update the Markdown files here when the hypotheses
change. The renderer checks that every hypothesis has a matching gloss.

`holbuild` builds the necessary theories at the project's HOL pin. The
pinned HOL executable then reads the built objects and uses `pandoc`
locally for the HTML. For the target only, the renderer keeps a temporary
`lowering/compilerCorrectnessDossierTargetScript.sml` until the render
exits. The draft admission is confined to that presentation theory.

The index follows definitions to the compiler, contract checker, source
interpreter entry points, verifereum, and HOL libraries. Boundary links
use the checked-out commit and resolved dependency pins. The renderer
rejects tracked changes before building so the links match the committed
definitions. The proof status beside each theorem comes from the loaded
theorem.

The default uses the pinned HOL exporter. To reproduce a review page
that records a dossier exporter patch, use a HOL checkout at that exact
exporter commit and pass it to `--exporter`:

```sh
git -C "$hol_repo" worktree add --detach "$exporter_checkout" "$exporter_revision"
python3 tools/statement-dossier/render.py \
  --exporter "$exporter_checkout" --output /path/to/compiler-correctness.html
```

For the target page, add `--draft` with the recorded draft revision and
path. If the recorded vyper-hol commit predates these tools, copy this
directory into `tools/statement-dossier/` in a worktree at that commit.
The renderer loads `statementDossierLib.sml` from the exporter checkout's
`HEAD`. It builds and reads theories on the project's HOL pin.
