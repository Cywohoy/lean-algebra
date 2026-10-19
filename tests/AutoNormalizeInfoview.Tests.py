"""Check Lean server goal states and tactic hover help, fresh and after editing."""

import json
import os
from pathlib import Path
import queue
import shutil
import subprocess
import threading
import time


workspace = Path(__file__).resolve().parents[1]
lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake.exe")
server = subprocess.Popen(
    [lake, "env", "lean", "--server"],
    cwd=workspace,
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.DEVNULL,
    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
)
messages = queue.Queue()
request_id = 0
diagnostics = []


def read_messages():
    while True:
        headers = {}
        while True:
            line = server.stdout.readline()
            if not line:
                messages.put(None)
                return
            if line in (b"\r\n", b"\n"):
                break
            key, value = line.decode("ascii").split(":", 1)
            headers[key.lower()] = value.strip()
        body = server.stdout.read(int(headers["content-length"]))
        messages.put(json.loads(body))


threading.Thread(target=read_messages, daemon=True).start()


def write_message(message):
    body = json.dumps(message, ensure_ascii=False).encode("utf-8")
    server.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body)
    server.stdin.flush()


def send(method, params, id=None):
    message = {"jsonrpc": "2.0", "method": method, "params": params}
    if id is not None:
        message["id"] = id
    write_message(message)


def request(method, params):
    global request_id
    request_id += 1
    id = request_id
    send(method, params, id)
    deadline = time.monotonic() + 60
    while True:
        message = messages.get(timeout=max(0.1, deadline - time.monotonic()))
        if message is None:
            raise AssertionError("Lean server exited before responding")
        if message.get("method") == "textDocument/publishDiagnostics":
            diagnostics.extend(message["params"]["diagnostics"])
        if "method" in message and "id" in message:
            method = message["method"]
            if method == "workspace/configuration":
                value = [None] * len(message.get("params", {}).get("items", []))
            elif method in ("client/registerCapability", "workspace/semanticTokens/refresh",
                            "workspace/inlayHint/refresh", "workspace/codeLens/refresh",
                            "workspace/diagnostic/refresh"):
                value = None
            else:
                raise AssertionError(f"Unexpected server request: {method}")
            write_message({"jsonrpc": "2.0", "id": message["id"], "result": value})
        elif message.get("id") == id:
            assert "error" not in message, message
            return message["result"]
        if time.monotonic() >= deadline:
            raise TimeoutError(f"Lean server did not answer {method}")


source = """import AlgebraBook.Sets
import AlgebraBook.Tactic.Auto
import Ample.Tactic
open Course
open scoped Course.Auto Classical

example {A : Type} (S : Set A) : Sᶜᶜ ⊆ S := by
  intro x hxScc
  expand at hxScc
  expand at hxScc
  
  exact hxScc

example (n : Int) : ¬ n < 0 → 0 ≤ n := by
  intro h
  
  exact h

theorem display_not_mem {A : Type} (S : Set A) (x : A)
    (h : ¬ (x ∈ S)) : ¬ (x ∈ S) := by
  have hCopy := h
  
  exact hCopy

theorem display_compl {A : Type} (S : Set A) (x : A)
    (h : x ∈ Sᶜ) : x ∈ Sᶜ := by
  have hCopy := h
  
  exact hCopy

example (n : Nat) (h : 0 < n) : n ∈ positives := by
  dsimp [positives]
  dsimp [positive]
  exact h

theorem display_indiscern_hyp (f g : Nat → Nat) (h : f = g) : ∀ x, f x = g x := by
  indiscern at h
  
  exact h

theorem display_ext_hyp (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext at h
  
  exact h

theorem display_indiscern_goal (f g : Nat → Nat) (h : f = g) (x : Nat) : f x = g x := by
  indiscern
  
  exact h

theorem display_named_comparisons (a b c d : Nat)
    (h : (a, c) = (b, d)) : a = b ∧ c = d := by
  constructor with first second
  indisc goals first second with pair
  
  exact h

theorem display_forward_apply (P Q : Prop) (r : P → Q) (hp : P) : Q := by
  apply r at hp with hq
  
  exact hq

theorem display_constructor_forward (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor at hp hq with combined
  
  exact combined

theorem display_unpack_goals (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  constructor with first second
  unpack goals first second with combined
  
  exact h

theorem display_unpack_hypothesis (P Q : Prop) (h : P ∧ Q) : Q := by
  unpack h with ⟨hp, hq⟩
  
  exact hq

theorem display_finished_expansion (n : Nat) : (fun x => x) n = n := by
  expand
  

theorem display_finish_keeps_sibling (n m : Nat) : (n + 0 = n) ∧ (m = m) := by
  constructor with first second
  rw [Nat.add_zero]
  
  rfl

theorem display_apply_order : ∃ n : Nat, n = 7 := by
  apply Exists.intro with certificate value
  
  case certificate => rfl

theorem display_recursive_comparison (p q : Fin 3 × Fin 4) (h : p = q) :
    p.1.val = q.1.val := by
  indisc at h with first second
  
  exact first

theorem display_congruence_hover (f g h : Nat → Nat) (x : Nat)
    (hgh : ∀ x, g x = h x) : f (g x) = f (h x) := by
  congr : 1
  exact hgh x

theorem display_arithmetic_hover (n : Nat) : 2 * n ≠ 5 := by
  arith

theorem display_suffices_hover (m : Nat) (ym : Fin m) : ym.val % m = ym.val := by
  suffices bound : ym.val < m by arith
  exact ym.isLt

set_option course.autoNormalize false in
theorem display_hover_without_normalization (n : Nat) : (fun x => x) n = n := by
  expand

theorem display_hover_in_brackets (P : Prop) (h : P) : P ∧ P := by {
  constructor with first second
  case first => exact h
  case second => exact h
}
"""
uri = (workspace / "tests/AutoNormalizeInfoview.lean").as_uri()
lines = source.splitlines()


def goal(line, character):
    result = request("$/lean/plainGoal", {
        "textDocument": {"uri": uri},
        "position": {"line": line, "character": character},
    })
    assert result is not None, (line, character)
    return result["goals"]


def check_goals():
    intro = lines.index("  intro x hxScc")
    initial = goal(intro, len(lines[intro]))
    assert "hxScc : x ∈ Sᶜᶜ" in initial[0], initial
    assert "⊢ x ∈ S" in initial[0], initial
    first_expand = intro + 1
    intermediate = goal(first_expand, len(lines[first_expand]))
    assert "hxScc : x ∉ Sᶜ" in intermediate[0], intermediate
    assert "⊢ x ∈ S" in intermediate[0], intermediate
    last_expand = intro + 2
    at_end = goal(last_expand, len(lines[last_expand]))
    below = goal(last_expand + 1, 2)
    assert at_end == below, (at_end, below)
    assert "hxScc : x ∈ S" in at_end[0] and "¬¬" not in at_end[0], at_end
    arithmetic_intro = lines.index("  intro h")
    at_end = goal(arithmetic_intro, len(lines[arithmetic_intro]))
    below = goal(arithmetic_intro + 1, 2)
    assert at_end == below, (at_end, below)
    assert "h : 0 ≤ n" in at_end[0], at_end
    for name, notation in (("display_not_mem", "x ∉ S"), ("display_compl", "x ∈ Sᶜ")):
        declaration = next(i for i, line in enumerate(lines) if line.startswith("theorem " + name))
        step = declaration + 2
        at_end = goal(step, len(lines[step]))
        below = goal(step + 1, 2)
        assert at_end == below, (at_end, below)
        assert "h hCopy : " + notation in at_end[0], at_end
        assert "⊢ " + notation in at_end[0], at_end
    dsimp = lines.index("  dsimp [positives]")
    first = goal(dsimp, len(lines[dsimp]))
    second = goal(dsimp + 1, len(lines[dsimp + 1]))
    assert "⊢ positive n" in first[0], first
    assert "⊢ 0 < n" in second[0], second
    for name, expected in (("display_indiscern_hyp", "h : ∀"),
                           ("display_ext_hyp", "h : f = g"),
                           ("display_indiscern_goal", "⊢ f = g")):
        declaration = next(i for i, line in enumerate(lines) if line.startswith("theorem " + name))
        step = declaration + 1
        at_end = goal(step, len(lines[step]))
        below = goal(step + 1, 2)
        assert at_end == below, (name, at_end, below)
        assert expected in at_end[0], (name, at_end)
    for name, offset, expected in (("display_named_comparisons", 3, "case pair"),
                                   ("display_forward_apply", 1, "hq : Q"),
                                   ("display_constructor_forward", 1, "combined : P ∧ Q"),
                                   ("display_unpack_goals", 2, "case combined"),
                                   ("display_unpack_hypothesis", 1, "hq : Q")):
        declaration = next(i for i, line in enumerate(lines) if line.startswith("theorem " + name))
        step = declaration + offset
        at_end = goal(step, len(lines[step]))
        below = goal(step + 1, 2)
        assert at_end == below, (name, at_end, below)
        assert expected in at_end[0], (name, at_end)
    declaration = next(i for i, line in enumerate(lines) if line.startswith("theorem display_finished_expansion"))
    step = declaration + 1
    assert goal(step, len(lines[step])) == [], goal(step, len(lines[step]))
    assert goal(step + 1, 2) == [], goal(step + 1, 2)
    for name, offset, expected in (("display_finish_keeps_sibling", 2, "case second"),
                                   ("display_apply_order", 1, "case certificate"),
                                   ("display_recursive_comparison", 2, "first")):
        declaration = next(i for i, line in enumerate(lines) if line.startswith("theorem " + name))
        step = declaration + offset
        at_end = goal(step, len(lines[step]))
        below = goal(step + 1, 2)
        assert at_end == below, (name, at_end, below)
        assert expected in at_end[0], (name, at_end)
    assert not [d for d in diagnostics if d.get("severity") == 1], diagnostics


def check_hovers():
    for declaration_name, tactic_line, keyword in (
        ("display_not_mem", "  exact hCopy", "exact"),
        ("display_named_comparisons", "  constructor with first second", "constructor"),
        ("display_named_comparisons", "  indisc goals first second with pair", "indisc"),
        ("display_forward_apply", "  apply r at hp with hq", "apply"),
        ("display_ext_hyp", "  ext at h", "ext"),
        ("display_unpack_hypothesis", "  unpack h with ⟨hp, hq⟩", "unpack"),
        ("display_finished_expansion", "  expand", "expand"),
        ("display_recursive_comparison", "  indisc at h with first second", "indisc"),
        ("display_congruence_hover", "  congr : 1", "congr"),
        ("display_arithmetic_hover", "  arith", "arith"),
        ("display_suffices_hover", "  suffices bound : ym.val < m by arith", "suffices"),
        ("display_hover_without_normalization", "  expand", "expand"),
        ("display_hover_in_brackets", "  constructor with first second", "constructor"),
    ):
        declaration = next(i for i, line in enumerate(lines)
                           if line.startswith("theorem " + declaration_name))
        line = lines.index(tactic_line, declaration)
        character = lines[line].index(keyword) + 1
        result = request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": character},
        })
        assert result is not None, (declaration_name, "missing hover")
        value = result["contents"]["value"]
        assert "A sequence of tactics" not in value, (declaration_name, value)
        assert keyword in value, (declaration_name, value)
        assert not any("\uac00" <= c <= "\ud7a3" for c in value), (declaration_name, value)
        # The help must belong to this tactic, rather than its enclosing block.
        assert result["range"]["start"]["line"] == line, (declaration_name, result)
        assert result["range"]["end"]["line"] == line, (declaration_name, result)

    declaration = next(i for i, line in enumerate(lines)
                       if line.startswith("theorem display_forward_apply"))
    line = lines.index("  apply r at hp with hq", declaration)
    result = request("textDocument/hover", {
        "textDocument": {"uri": uri},
        "position": {"line": line, "character": lines[line].index("r at")},
    })
    assert result is not None and "P → Q" in result["contents"]["value"], result


try:
    request("initialize", {"processId": os.getpid(), "rootUri": workspace.as_uri(), "capabilities": {}})
    send("initialized", {})
    send("textDocument/didOpen", {"textDocument": {
        "uri": uri, "languageId": "lean4", "version": 1, "text": source,
    }})
    check_goals()
    check_hovers()
    send("textDocument/didChange", {
        "textDocument": {"uri": uri, "version": 2},
        "contentChanges": [{"text": source + "\n"}],
    })
    check_goals()
    check_hovers()
    send("textDocument/didClose", {"textDocument": {"uri": uri}})
    request("shutdown", None)
    send("exit", None)
    server.wait(timeout=10)
    print("PASS: goal states and tactic hover help, fresh and after incremental editing")
finally:
    if server.poll() is None:
        server.terminate()
        server.wait(timeout=10)
