// The pilot has explicit, top-level theorem declarations with tactic proofs.
// Keep their statements immutable in proof mode and preserve the complete draft.
export function exerciseModel(original, draft = original) {
  const starts = [...original.matchAll(/^theorem (exercise_\w+)\b/gm)];
  if (!starts.length) throw new Error('No exercise declarations found.');
  const parts = starts.map((match, index) => {
    const text = original.slice(match.index, starts[index + 1]?.index ?? original.length);
    const boundary = /:= by[^\S\n]*\n/.exec(text);
    if (!boundary) throw new Error('The exercise requires a multiline tactic proof.');
    const end = boundary.index + boundary[0].length;
    return {name: match[1], header: text.slice(0, end), body: text.slice(end).trimEnd() || '  '};
  });
  function parse(source) {
    const bodies = [];
    let cursor = 0;
    for (const [index, part] of parts.entries()) {
      if (!source.startsWith(part.header, cursor)) return null;
      cursor += part.header.length;
      const next = parts[index + 1];
      const end = next ? source.indexOf('\n' + next.header, cursor) : source.length;
      if (end < 0) return null;
      const body = source.slice(cursor, end).trimEnd();
      // Top-level helpers belong in the complete-code view.
      if (body.split('\n').some(line => line && !/^\s|^--/.test(line))) return null;
      bodies.push(body || '  ');
      cursor = end + (next ? 1 : 0);
    }
    return bodies;
  }
  const bodies = parse(draft);
  return {
    parts, parse, bodies: bodies || parts.map(part => part.body), full: !bodies,
    source(values) { return parts.map((part, i) => part.header + values[i]).join('\n\n'); },
    start(values, index) {
      return parts.slice(0, index).reduce((n, part, i) => n + part.header.length + values[i].length + 2, 0)
        + parts[index].header.length;
    },
  };
}
