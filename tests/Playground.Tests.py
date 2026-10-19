"""Check real Lean diagnostics, cursor goals, retained context, and isolated edits."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from web.lean_rpc import Playground, close_scopes


class PlaygroundTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.playground = Playground(ROOT, {
            'logic': {'before': 'import AlgebraBook.Tactic.Rule\nnamespace BrowserExample\n'},
            'arith': {'before': 'import AlgebraBook.Tactic.Arithmetic\nopen scoped Ample\n'},
            'context': {'before': 'import AlgebraBook.Tactic.Rule\nnamespace Earlier\ndef known := 7\n'},
        })

    @classmethod
    def tearDownClass(cls):
        cls.playground.close()

    def test_real_goals_and_corrected_proof(self):
        code = 'example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by\n  apply hPQ\n  sorry'
        result = self.playground.check({'snippet': 'logic', 'code': code,
            'position': {'line': 1, 'character': len('  apply hPQ')}})
        self.assertIn('⊢ P', '\n'.join(result['goal']))
        self.assertTrue(any('sorry' in item['message'] for item in result['diagnostics']))
        self.assertTrue(any(item['kind'] == 'unfinished' for item in result['diagnostics']))
        self.assertEqual(result['contextErrors'], [])
        revised = code.replace('sorry', 'exact hP')
        result = self.playground.check({'snippet': 'logic', 'code': revised,
            'session': result['session'], 'position': {'line': 2, 'character': len('  exact hP')}})
        self.assertEqual(result['goal'], [])
        self.assertFalse(any(item.get('severity') == 1 for item in result['diagnostics']))
        cursor = self.playground.goal({'session': result['session'], 'version': result['version'],
            'position': {'line': 1, 'character': len('  apply hPQ')}})
        self.assertIn('⊢ P', '\n'.join(cursor['goal']))

    def test_errors_are_mapped_to_editable_code(self):
        code = 'example : False := by\n  exact True.intro'
        result = self.playground.check({'snippet': 'logic', 'code': code})
        errors = [item for item in result['diagnostics'] if item.get('severity') == 1]
        self.assertTrue(errors, result)
        self.assertEqual(errors[0]['line'], 2)
        self.assertEqual(errors[0]['kind'], 'diagnostic')
        # Complete a partial theorem name in the actual Lean context, including
        # replacement of the suffix when the cursor is inside an identifier.
        code = 'example (a b : Nat) (h : a < b) : a + 3 < b + 3 := by\n  apply Nat.add_lt_add_rZZ'
        column = len(code.split('\n')[-1]) - 2
        completion = self.playground.complete({'snippet': 'logic', 'code': code,
            'session': result['session'], 'position': {'line': 1, 'character': column}})
        item = next(item for item in completion['items'] if item['label'] == 'add_lt_add_right')
        self.assertEqual(item['range'], {'start': {'line': 1, 'character': 12},
            'end': {'line': 1, 'character': len(code.split('\n')[-1])}})
        detail = self.playground.resolve({**completion, 'index': item['index']})
        self.assertIn('n + k < m + k', detail['detail'])
        # The preceding book context participates in completion. Switching the
        # example must invalidate both its definitions and old completion IDs.
        contextual = self.playground.complete({'snippet': 'context', 'code': '#check kno',
            'session': result['session'], 'position': {'line': 0, 'character': 10}})
        self.assertTrue(any(item['label'] == 'known' for item in contextual['items']), contextual)
        with self.assertRaises(ValueError):
            self.playground.resolve({**completion, 'index': item['index']})

    def test_goal_on_an_empty_indented_proof_line(self):
        code = ('theorem exercise_add_three_preserves_lt (a b : Nat)\n'
                '    (h : a < b) :\n'
                '    a + 3 < b + 3 := by\n  ')
        result = self.playground.check({'snippet': 'logic', 'code': code,
            'position': {'line': 3, 'character': 2}})
        self.assertIn('a + 3 < b + 3', '\n'.join(result['goal'] or []), result)
        pending = [item for item in result['diagnostics'] if item['kind'] == 'unfinished']
        self.assertTrue(pending, result)
        self.assertTrue(all(item['kind'] == 'unfinished' for item in result['diagnostics'] if item.get('severity') == 1))
        code += 'apply Nat.add_lt_add_right\n  '
        result = self.playground.check({'snippet': 'logic', 'code': code,
            'session': result['session'], 'position': {'line': 4, 'character': 2}})
        self.assertIn('⊢ a < b', '\n'.join(result['goal'] or []), result)

    def test_ample_automation_is_available(self):
        result = self.playground.check({'snippet': 'arith',
            'code': 'example (n : Nat) : 2 * n ≠ 5 := by\n  arith'})
        self.assertEqual(result['contextErrors'], [])
        self.assertFalse(any(item.get('severity') == 1 for item in result['diagnostics']), result)

    def test_context_switching_reuses_session(self):
        first = self.playground.check({'snippet': 'context', 'code': 'example : known = 7 := by rfl'})
        second = self.playground.check({'snippet': 'logic', 'session': first['session'],
            'code': '#check Earlier.known'})
        self.assertEqual(first['session'], second['session'])
        self.assertTrue(any(item.get('severity') == 1 for item in second['diagnostics']), second)

    def test_preceding_definitions_and_session_isolation(self):
        good = self.playground.check({'snippet': 'context', 'code': 'example : known = 7 := by rfl'})
        self.assertFalse(any(item.get('severity') == 1 for item in good['diagnostics']), good)
        self.playground.check({'snippet': 'logic', 'code': 'def privateDraft := 3'})
        other = self.playground.check({'snippet': 'logic', 'code': '#check privateDraft'})
        self.assertTrue(any(item.get('severity') == 1 for item in other['diagnostics']), other)

    def test_scopes_and_invalid_input(self):
        self.assertEqual(close_scopes('namespace A\nsection\nend\n'), '\nend A\n')
        with self.assertRaises(ValueError):
            self.playground.check({'snippet': 'missing', 'code': ''})


if __name__ == '__main__':
    unittest.main()
