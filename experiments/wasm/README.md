# Browser Lean feasibility experiment

This directory tests browser-side compilation separately from the published book.
It does not change the book's Lean toolchain, add a server backend, or enable a
partially compatible editor on GitHub Pages. The HTTP server serves static files
on loopback; all proof checking runs inside a browser Web Worker.

## Result: 20 October 2026

Tested in desktop Chrome with the pinned runtime below, using both ordinary
COOP/COEP response headers and a Service Worker on a server without those headers.

| Probe | Observed result |
| --- | --- |
| `intro`, `apply`, `exact` | Accepted a complete implication proof |
| Arithmetic | Accepted `2 * n ≠ 5` using the runtime's built-in `omega` |
| Textbook mathematics | Accepted the actual `Set`, membership, `Subset`, and `subset_trans` source extracted from Ample |
| False equality | Rejected `2 + 2 = 5` proved by `rfl` |
| Incomplete proof | Reported `P Q : Prop`, `hp : P`, and goal `Q` |
| Explicit proof-state trace | Returned assumptions and goal at `trace_state` |
| User-defined tactic macro | Defined and executed `finish_trivial` in the submitted source |
| `import Lean` | Failed: the minimal downloaded fixture contains only the Init library closure |
| Existing Ample build | Rejected `Ample.Tactic.Classical.olean` with `incompatible header` |
| Isolation without server headers | The pinned COI Service Worker changed `crossOriginIsolated` from false to true; the same compiler probes then ran |

The last two import failures are compatibility boundaries, not successful Ample
tests. No complete Ample tactic module has been rebuilt or executed in this
experiment. The mathematical-source probe uses core tactics; it does not test
`arith`, `ext`, `indisc`, `expand`, or automatic normalization.

The tested compiler Worker exposes compilation and diagnostic messages. This
adapter does not implement the book editor's cursor-based goal queries, hover,
completion, cancellation, or incremental LSP/RPC session. An unsolved-goal
diagnostic or a manually inserted `trace_state` is not a replacement for those
features.

Local boot, including the first Init import, took about 2.5–4 seconds. These tiny
proofs subsequently took about 4–150 milliseconds. This was a desktop loopback
test, not a cold internet download or a mobile benchmark. The full WASM binary
is 100,838,905 bytes, and the Init library fixture is 79,760,876 bytes before
transport compression. The upstream Worker initially requests a 2 GiB shared
WebAssembly memory on desktop; this is not a measurement of resident RAM.

## Compatibility decision

Browser execution is feasible, but this runtime is not a drop-in replacement for
the current Lean 4.35 editor. The downloaded fork is based on Lean 4.33 and uses
32-bit WASM library artifacts. The existing Ample artifacts use the native
64-bit Lean 4.35 toolchain. They cannot be mixed; the observed header rejection
does not isolate version mismatch from word-size mismatch.

Further WASM integration should proceed in this order:

1. Build a WASM Lean and its matching Init/Std/Lean libraries for the book's
   pinned version, or evaluate a deliberate version migration separately.
2. Rebuild Ample for that exact toolchain, including the interpreter artifacts
   and initialization support required by its metaprogramming code. Run the
   existing tactic and proof-state regressions against the result.
3. Implement the editor's goal, hover, completion, interruption, and diagnostic
   interfaces. Preserve the distinction between an incomplete proof and an
   invalid proof.
4. Measure cold downloads, memory, caching, and mobile behavior. Validate the
   isolated experiment under the actual `/lean-algebra/` GitHub Pages prefix;
   the Service Worker test here uses localhost, not the deployed site.

If matching-toolchain builds or editor support require substantial maintenance,
the next alternatives remain a Lean server connected to the book editor, or
Codespaces with the existing project and toolchain. Neither is provisioned by
this experiment.

## Reproduction

Requirements: Node, Git, tar, Chrome, Playwright, and the sibling Ample checkout
with its native `Ample.Tactic.Classical` build. Run from the Textbook root.
The scripts use a regular `playwright` installation; in this workspace they can
also find the bundled runtime installation. Binary downloads and generated
reports stay under ignored `tmp/wasm/`.

```text
git clone https://github.com/cauli/lean4-wasm-in-browser.git tmp/wasm/upstream
git -C tmp/wasm/upstream checkout 017c835ecf0ac8c74745a867c65faeac0baf6654
node tmp/wasm/upstream/tests/fetch-artifacts.mjs
git clone https://github.com/gzuidhof/coi-serviceworker.git tmp/wasm/coi-serviceworker
git -C tmp/wasm/coi-serviceworker checkout 7b1d2a092d0d2dd2b7270b6f12f13605de26f214
node experiments/wasm/browser-tests.cjs
node experiments/wasm/browser-tests.cjs --service-worker
node experiments/wasm/server.cjs
```

The final command prints a local URL for manual editing. Press **Start Lean**,
then **Check proof**. Diagnostic JSON is intentionally shown directly in this
developer experiment. The public book does not include this UI.

Reports are written to `tmp/wasm/browser-results.json` and
`tmp/wasm/browser-results-sw.json`. They include the exact submitted sources,
diagnostics, timing, and browser version. Non-GET requests fail the test: proof
text is sent only to the Worker, not to an HTTP compiler endpoint.

## Upstream pins and licenses

- [Lean WASM experiment](https://github.com/cauli/lean4-wasm-in-browser),
  commit `017c835ecf0ac8c74745a867c65faeac0baf6654`, Apache-2.0.
  Its [runtime manifest](https://github.com/cauli/lean4-wasm-in-browser/blob/017c835ecf0ac8c74745a867c65faeac0baf6654/deploy/runtime-release.json)
  pins Lean commit `62b6a2291302d4bbeace37642a066b7510d0145c` and Emscripten
  4.0.22. The fixture fetcher verifies archive and runtime SHA-256 checksums.
- [COI Service Worker](https://github.com/gzuidhof/coi-serviceworker),
  commit `7b1d2a092d0d2dd2b7270b6f12f13605de26f214`, MIT.

The experiment serves upstream files from their checked-out directories without
modifying or copying them into this repository. Their notices and licenses
remain in those directories. Retain the notices and applicable licenses if
these assets are later packaged for public deployment.
